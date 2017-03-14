//===-- Dependency.cpp - Memory location dependency -------------*- C++ -*-===//
//
//               The Tracer-X KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// This file contains the implementation of the dependency analysis to
/// compute the locations upon which the unsatisfiability core depends,
/// which is used in computing the interpolant.
///
//===----------------------------------------------------------------------===//

#include "Dependency.h"
#include "ShadowArray.h"
#include "TxPrintUtil.h"

#include "klee/CommandLine.h"
#include "klee/Internal/Support/ErrorHandling.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 5)
#include <llvm/IR/DebugInfo.h>
#elif LLVM_VERSION_CODE >= LLVM_VERSION(3, 2)
#include <llvm/DebugInfo.h>
#else
#include <llvm/Analysis/DebugInfo.h>
#endif

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Intrinsics.h>
#else
#include <llvm/Constants.h>
#include <llvm/DataLayout.h>
#include <llvm/Intrinsics.h>
#endif

using namespace klee;

namespace klee {

void StoredValue::init(ref<VersionedValue> vvalue,
                       std::set<const Array *> &replacements,
                       std::set<std::string> &_coreReasons, bool shadowing) {
  std::set<ref<MemoryLocation> > locations = vvalue->getLocations();

  refCount = 0;
  id = reinterpret_cast<uintptr_t>(this);
  expr = shadowing ? ShadowArray::getShadowExpression(vvalue->getExpression(),
                                                      replacements)
                   : vvalue->getExpression();
  value = vvalue->getValue();

  doNotUseBound = !(vvalue->canInterpolateBound());

  coreReasons = _coreReasons;

  if (doNotUseBound)
    return;

  if (!locations.empty()) {
    // Here we compute memory bounds for checking pointer values. The memory
    // bound is the size of the allocation minus the offset; this is the weakest
    // precondition (interpolant) of memory bound checks done by KLEE.
    for (std::set<ref<MemoryLocation> >::iterator it = locations.begin(),
                                                  ie = locations.end();
         it != ie; ++it) {
      llvm::Value *v = (*it)->getValue(); // The allocation site

      // Concrete bound
      uint64_t concreteBound = (*it)->getConcreteOffsetBound();
      std::set<ref<Expr> > newBounds;

      if (concreteBound > 0)
        allocationBounds[v].insert(Expr::createPointer(concreteBound));

      // Symbolic bounds
      std::set<ref<Expr> > bounds = (*it)->getSymbolicOffsetBounds();

      if (shadowing) {
        std::set<ref<Expr> > shadowBounds;
        for (std::set<ref<Expr> >::iterator it1 = bounds.begin(),
                                            ie1 = bounds.end();
             it1 != ie1; ++it1) {
          shadowBounds.insert(
              ShadowArray::getShadowExpression(*it1, replacements));
        }
        bounds = shadowBounds;
      }

      if (!bounds.empty())
        allocationBounds[v].insert(bounds.begin(), bounds.end());

      ref<Expr> offset = shadowing ? ShadowArray::getShadowExpression(
                                         (*it)->getOffset(), replacements)
                                   : (*it)->getOffset();

      // We next build the offsets to be compared against stored allocation
      // offset bounds
      ConstantExpr *oe = llvm::dyn_cast<ConstantExpr>(offset);
      if (oe && !allocationOffsets[v].empty()) {
        // Here we check if smaller offset exists, in which case we replace it
        // with the new offset; as we want the greater offset to possibly
        // violate an offset bound.
        std::set<ref<Expr> > res;
        uint64_t offsetInt = oe->getZExtValue();
        for (std::set<ref<Expr> >::iterator it1 = allocationOffsets[v].begin(),
                                            ie1 = allocationOffsets[v].end();
             it1 != ie1; ++it1) {
          if (ConstantExpr *ce = llvm::dyn_cast<ConstantExpr>(*it1)) {
            uint64_t c = ce->getZExtValue();
            if (offsetInt > c) {
              res.insert(offset);
              continue;
            }
          }
          res.insert(*it1);
        }
        allocationOffsets[v] = res;
      } else {
        allocationOffsets[v].insert(offset);
      }
    }
  }
}

ref<Expr> StoredValue::getBoundsCheck(ref<StoredValue> stateValue,
                                      std::set<ref<Expr> > &bounds,
                                      int debugSubsumptionLevel) const {
  ref<Expr> res;
#ifdef ENABLE_Z3

  // In principle, for a state to be subsumed, the subsuming state must be
  // weaker, which in this case means that it should specify less allocations,
  // so all allocations in the subsuming (this), should be specified by the
  // subsumed (the stateValue argument), and we iterate over allocation of
  // the current object and for each such allocation, retrieve the
  // information from the argument object; in this way resulting in
  // less iterations compared to doing it the other way around.
  bool matchFound = false;
  for (std::map<llvm::Value *, std::set<ref<Expr> > >::const_iterator
           it = allocationBounds.begin(),
           ie = allocationBounds.end();
       it != ie; ++it) {
    std::set<ref<Expr> > tabledBounds = it->second;
    std::map<llvm::Value *, std::set<ref<Expr> > >::iterator iter =
        stateValue->allocationOffsets.find(it->first);
    if (iter == stateValue->allocationOffsets.end()) {
      continue;
    }
    matchFound = true;

    std::set<ref<Expr> > stateOffsets = iter->second;

    assert(!tabledBounds.empty() && "tabled bounds empty");

    if (stateOffsets.empty()) {
      if (debugSubsumptionLevel >= 3) {
        std::string msg;
        llvm::raw_string_ostream stream(msg);
        it->first->print(stream);
        stream.flush();
        klee_message("No offset defined in state for %s", msg.c_str());
      }
      return ConstantExpr::create(0, Expr::Bool);
    }

    for (std::set<ref<Expr> >::const_iterator it1 = stateOffsets.begin(),
                                              ie1 = stateOffsets.end();
         it1 != ie1; ++it1) {
      for (std::set<ref<Expr> >::const_iterator it2 = tabledBounds.begin(),
                                                ie2 = tabledBounds.end();
           it2 != ie2; ++it2) {
        if (ConstantExpr *tabledBound = llvm::dyn_cast<ConstantExpr>(*it2)) {
          uint64_t tabledBoundInt = tabledBound->getZExtValue();
          if (ConstantExpr *stateOffset = llvm::dyn_cast<ConstantExpr>(*it1)) {
            if (tabledBoundInt > 0) {
              uint64_t stateOffsetInt = stateOffset->getZExtValue();
              if (stateOffsetInt >= tabledBoundInt) {
                if (debugSubsumptionLevel >= 3) {
                  std::string msg;
                  llvm::raw_string_ostream stream(msg);
                  it->first->print(stream);
                  stream.flush();
                  klee_message("Offset %lu out of bound %lu for %s",
                               stateOffsetInt, tabledBoundInt, msg.c_str());
                }
                return ConstantExpr::create(0, Expr::Bool);
              }
            }
          }

          if (tabledBoundInt > 0) {
            // Symbolic state offset, but concrete tabled bound. Here the bound
            // is known (non-zero), so we create constraints
            if (res.isNull()) {
              res = UltExpr::create(*it1, *it2);
            } else {
              res = AndExpr::create(UltExpr::create(*it1, *it2), res);
            }
            bounds.insert(*it2);
          }
          continue;
        }
        // Create constraints for symbolic bounds
        if (res.isNull()) {
          res = UltExpr::create(*it1, *it2);
        } else {
          res = AndExpr::create(UltExpr::create(*it1, *it2), res);
        }
        bounds.insert(*it2);
      }
    }
  }

  // Bounds check successful if no constraints added
  if (res.isNull()) {
    if (matchFound)
      return ConstantExpr::create(1, Expr::Bool);
    else
      return ConstantExpr::create(0, Expr::Bool);
  }
#endif // ENABLE_Z3
  return res;
}

void StoredValue::print(llvm::raw_ostream &stream) const { print(stream, ""); }

void StoredValue::print(llvm::raw_ostream &stream,
                        const std::string &prefix) const {
  std::string nextTabs = appendTab(prefix);

  if (!doNotUseBound && !allocationBounds.empty()) {
    stream << prefix << "BOUNDS:";
    for (std::map<llvm::Value *, std::set<ref<Expr> > >::const_iterator
             it = allocationBounds.begin(),
             ie = allocationBounds.end();
         it != ie; ++it) {
      std::set<ref<Expr> > boundsSet = it->second;
      stream << "\n";
      stream << prefix << "[";
      it->first->print(stream);
      stream << "<={";
      for (std::set<ref<Expr> >::const_iterator it1 = it->second.begin(),
                                                is1 = it1,
                                                ie1 = it->second.end();
           it1 != ie1; ++it1) {
        if (it1 != is1)
          stream << ",";
        (*it1)->print(stream);
      }
      stream << "}]";
    }

    if (!allocationOffsets.empty()) {
      stream << "\n";
      stream << prefix << "OFFSETS:";
      for (std::map<llvm::Value *, std::set<ref<Expr> > >::const_iterator
               it = allocationOffsets.begin(),
               ie = allocationOffsets.end();
           it != ie; ++it) {
        std::set<ref<Expr> > boundsSet = it->second;
        stream << "\n";
        stream << prefix << "[";
        it->first->print(stream);
        stream << "=={";
        for (std::set<ref<Expr> >::const_iterator it1 = it->second.begin(),
                                                  is1 = it1,
                                                  ie1 = it->second.end();
             it1 != ie1; ++it1) {
          if (it1 != is1)
            stream << ",";
          (*it1)->print(stream);
        }
        stream << "}]";
      }
    }
  } else {
    stream << prefix;
    expr->print(stream);
  }

  if (!coreReasons.empty()) {
    stream << "\n";
    stream << prefix << "reason(s) for storage:\n";
    for (std::set<std::string>::const_iterator is = coreReasons.begin(),
                                               ie = coreReasons.end(), it = is;
         it != ie; ++it) {
      if (it != is)
        stream << "\n";
      stream << nextTabs << *it;
    }
  }
}

/**/

bool Dependency::isMainArgument(llvm::Value *loc) {
  llvm::Argument *vArg = llvm::dyn_cast<llvm::Argument>(loc);

  // FIXME: We need a more precise way to detect main argument
  if (vArg && vArg->getParent() &&
      (vArg->getParent()->getName().equals("main") ||
       vArg->getParent()->getName().equals("__user_main"))) {
    return true;
  }
  return false;
}

ref<VersionedValue>
Dependency::registerNewVersionedValue(llvm::Value *value,
                                      ref<VersionedValue> vvalue) {
  valuesMap[value].push_back(vvalue);
  return vvalue;
}

std::pair<Dependency::ConcreteStore, Dependency::SymbolicStore>
Dependency::getStoredExpressions(const std::vector<llvm::Instruction *> &stack,
                                 std::set<const Array *> &replacements,
                                 bool coreOnly) {
  ConcreteStore concreteStore;
  SymbolicStore symbolicStore;

  for (std::map<ref<MemoryLocation>,
                std::pair<ref<VersionedValue>, ref<VersionedValue> > >::iterator
           it = concretelyAddressedStore.begin(),
           ie = concretelyAddressedStore.end();
       it != ie; ++it) {
    if (!it->first->contextIsPrefixOf(stack))
      continue;
    if (it->second.second.isNull())
      continue;

    if (!coreOnly) {
      llvm::Value *base = it->first->getValue();
      concreteStore[base][it->first] = StoredValue::create(it->second.second);
    } else if (it->second.second->isCore()) {
      // An address is in the core if it stores a value that is in the core
      llvm::Value *base = it->first->getValue();
#ifdef ENABLE_Z3
      if (!NoExistential) {
        concreteStore[base][it->first] =
            StoredValue::create(it->second.second, replacements);
      } else
#endif
        concreteStore[base][it->first] = StoredValue::create(it->second.second);
    }
  }

  for (std::map<ref<MemoryLocation>,
                std::pair<ref<VersionedValue>, ref<VersionedValue> > >::iterator
           it = symbolicallyAddressedStore.begin(),
           ie = symbolicallyAddressedStore.end();
       it != ie; ++it) {
    if (!it->first->contextIsPrefixOf(stack))
      continue;

    if (it->second.second.isNull())
      continue;

    if (!coreOnly) {
      llvm::Value *base = it->first->getValue();
      symbolicStore[base].push_back(
          AddressValuePair(it->first, StoredValue::create(it->second.second)));
    } else if (it->second.second->isCore()) {
      // An address is in the core if it stores a value that is in the core
      llvm::Value *base = it->first->getValue();
#ifdef ENABLE_Z3
      if (!NoExistential) {
        symbolicStore[base].push_back(AddressValuePair(
            MemoryLocation::create(it->first, replacements),
            StoredValue::create(it->second.second, replacements)));
      } else
#endif
        symbolicStore[base].push_back(AddressValuePair(
            it->first, StoredValue::create(it->second.second)));
      }
  }

  return std::pair<ConcreteStore, SymbolicStore>(concreteStore, symbolicStore);
}

ref<VersionedValue>
Dependency::getLatestValueNoConstantCheck(llvm::Value *value,
                                          ref<Expr> valueExpr) {
  assert(value && "value cannot be null");

  if (valuesMap.find(value) != valuesMap.end()) {
    if (!valueExpr.isNull()) {
      // Slight complication here that the latest version of an LLVM
      // value may not be at the end of the vector; it is possible other
      // values in a call stack has been appended to the vector, before
      // the function returned, so the end part of the vector contains
      // local values in a call already returned. To resolve this issue,
      // here we naively search for values with equivalent expression.
      std::vector<ref<VersionedValue> > allValues = valuesMap[value];

      for (std::vector<ref<VersionedValue> >::reverse_iterator
               it = allValues.rbegin(),
               ie = allValues.rend();
           it != ie; ++it) {
        ref<Expr> e = (*it)->getExpression();
        if (e == valueExpr)
          return *it;
      }
    } else {
      return valuesMap[value].back();
    }
  }

  if (parent)
    return parent->getLatestValueNoConstantCheck(value, valueExpr);

  return 0;
}

ref<VersionedValue> Dependency::getLatestValueForMarking(llvm::Value *val,
                                                         ref<Expr> expr) {
  ref<VersionedValue> value = getLatestValueNoConstantCheck(val, expr);

  // Right now we simply ignore the __dso_handle values. They are due
  // to library / linking errors caused by missing options (-shared) in the
  // compilation involving shared library.
  if (value.isNull()) {
    if (llvm::ConstantExpr *cVal = llvm::dyn_cast<llvm::ConstantExpr>(val)) {
      for (unsigned i = 0; i < cVal->getNumOperands(); ++i) {
        if (cVal->getOperand(i)->getName().equals("__dso_handle")) {
          return value;
        }
      }
    }

    if (llvm::isa<llvm::Constant>(val))
      return value;

    assert(!"unknown value");
  }
  return value;
}

void Dependency::updateStore(ref<MemoryLocation> loc,
                             ref<VersionedValue> address,
                             ref<VersionedValue> value) {
  if (loc->hasConstantAddress())
    concretelyAddressedStore[loc] =
        std::pair<ref<VersionedValue>, ref<VersionedValue> >(address, value);
  else
    symbolicallyAddressedStore[loc] =
        std::pair<ref<VersionedValue>, ref<VersionedValue> >(address, value);
}

void Dependency::addDependency(ref<VersionedValue> source,
                               ref<VersionedValue> target,
                               bool multiLocationsCheck) {
  if (source.isNull() || target.isNull())
    return;

  assert((!multiLocationsCheck || target->getLocations().empty()) &&
         "should not add new location");

  addDependencyIntToPtr(source, target);
}

void Dependency::addDependencyIntToPtr(ref<VersionedValue> source,
                                       ref<VersionedValue> target) {
  ref<MemoryLocation> nullLocation;

  if (source.isNull() || target.isNull())
    return;

  std::set<ref<MemoryLocation> > locations = source->getLocations();
  ref<Expr> targetExpr(ZExtExpr::create(target->getExpression(),
                                        Expr::createPointer(0)->getWidth()));
  for (std::set<ref<MemoryLocation> >::iterator it = locations.begin(),
                                                ie = locations.end();
       it != ie; ++it) {
    ref<Expr> sourceBase((*it)->getBase());
    ref<Expr> offsetDelta(SubExpr::create(
        SubExpr::create(targetExpr, sourceBase), (*it)->getOffset()));
    target->addLocation(MemoryLocation::create(*it, targetExpr, offsetDelta));
  }
  target->addDependency(source, nullLocation);
}

void Dependency::addDependencyWithOffset(ref<VersionedValue> source,
                                         ref<VersionedValue> target,
                                         ref<Expr> offsetDelta) {
  ref<MemoryLocation> nullLocation;

  if (source.isNull() || target.isNull())
    return;

  std::set<ref<MemoryLocation> > locations = source->getLocations();
  ref<Expr> targetExpr(target->getExpression());

  ConstantExpr *ce = llvm::dyn_cast<ConstantExpr>(targetExpr);
  uint64_t a = ce ? ce->getZExtValue() : 0;

  ConstantExpr *de = llvm::dyn_cast<ConstantExpr>(offsetDelta);
  uint64_t d = de ? de->getZExtValue() : 0;

  uint64_t nLocations = locations.size();
  uint64_t i = 0;
  bool locationAdded = false;

  for (std::set<ref<MemoryLocation> >::iterator it = locations.begin(),
                                                ie = locations.end();
       it != ie; ++it) {
    ++i;

    ConstantExpr *be = llvm::dyn_cast<ConstantExpr>((*it)->getBase());
    uint64_t b = be ? be->getZExtValue() : 0;

    ConstantExpr *oe = llvm::dyn_cast<ConstantExpr>((*it)->getOffset());
    uint64_t o = (oe ? oe->getZExtValue() : 0) + d;

    // The following if conditional implements a mechanism to
    // only add memory locations that make sense; that is, when
    // the offset is address minus base
    if (ce && de && be && oe) {
      if (o != (a - b) && (b != 0) && (locationAdded || i < nLocations))
        continue;
    }
    target->addLocation(MemoryLocation::create(*it, targetExpr, offsetDelta));
    locationAdded = true;
  }
  target->addDependency(source, nullLocation);
}

void Dependency::addDependencyViaLocation(ref<VersionedValue> source,
                                          ref<VersionedValue> target,
                                          ref<MemoryLocation> via) {
  if (source.isNull() || target.isNull())
    return;

  std::set<ref<MemoryLocation> > locations = source->getLocations();
  for (std::set<ref<MemoryLocation> >::iterator it = locations.begin(),
                                                ie = locations.end();
       it != ie; ++it) {
    target->addLocation(*it);
  }
  target->addDependency(source, via);
}

void Dependency::addDependencyViaExternalFunction(
    const std::vector<llvm::Instruction *> &stack, ref<VersionedValue> source,
    ref<VersionedValue> target) {
  if (source.isNull() || target.isNull())
    return;

#ifdef ENABLE_Z3
  if (!NoBoundInterpolation) {
    std::set<ref<MemoryLocation> > locations = source->getLocations();
    if (!locations.empty()) {
      std::string reason = "";
      if (debugSubsumptionLevel >= 1) {
        llvm::raw_string_ostream stream(reason);
        stream << "parameter [";
        source->getValue()->print(stream);
        stream << "] of external call [";
        target->getValue()->print(stream);
        stream << "]";
        stream.flush();
      }
      markPointerFlow(source, source, reason);
    }
  }
#endif

  // Add new location to the target in case of pointer return value
  llvm::Type *t = target->getValue()->getType();
  if (t->isPointerTy() && target->getLocations().size() == 0) {
    uint64_t size = 0;
    ref<Expr> address(target->getExpression());

    llvm::Type *elementType = t->getPointerElementType();
    if (elementType->isSized()) {
      size = targetData->getTypeStoreSize(elementType);
    }

    target->addLocation(
        MemoryLocation::create(target->getValue(), stack, address, size));
  }

  addDependencyToNonPointer(source, target);
}

void Dependency::addDependencyToNonPointer(ref<VersionedValue> source,
                                           ref<VersionedValue> target) {
  if (source.isNull() || target.isNull())
    return;

  ref<MemoryLocation> nullLocation;
  target->addDependency(source, nullLocation);
}

std::vector<ref<VersionedValue> >
Dependency::directFlowSources(ref<VersionedValue> target) const {
  std::vector<ref<VersionedValue> > ret;
  std::map<ref<VersionedValue>, ref<MemoryLocation> > sources =
      target->getSources();
  ref<VersionedValue> loadAddress = target->getLoadAddress(),
                      storeAddress = target->getStoreAddress();

  for (std::map<ref<VersionedValue>, ref<MemoryLocation> >::iterator it =
           sources.begin();
       it != sources.end(); ++it) {
    ret.push_back(it->first);
  }

  if (!loadAddress.isNull()) {
    ret.push_back(loadAddress);
    if (!storeAddress.isNull() && storeAddress != loadAddress) {
      ret.push_back(storeAddress);
    }
  } else if (!storeAddress.isNull()) {
    ret.push_back(storeAddress);
  }

  return ret;
}

void Dependency::markFlow(ref<VersionedValue> target,
                          const std::string &reason) const {
  if (target.isNull() || (target->isCore() && !target->canInterpolateBound()))
    return;

  target->setAsCore(reason);
  target->disableBoundInterpolation();

  std::vector<ref<VersionedValue> > stepSources = directFlowSources(target);
  for (std::vector<ref<VersionedValue> >::iterator it = stepSources.begin(),
                                                   ie = stepSources.end();
       it != ie; ++it) {
    markFlow(*it, reason);
  }
}

void Dependency::markPointerFlow(ref<VersionedValue> target,
                                 ref<VersionedValue> checkedAddress,
                                 std::set<ref<Expr> > &bounds,
                                 const std::string &reason) const {
  if (target.isNull())
    return;

  if (target->canInterpolateBound()) {
    //  checkedAddress->dump();
    std::set<ref<MemoryLocation> > locations = target->getLocations();
    for (std::set<ref<MemoryLocation> >::iterator it = locations.begin(),
                                                  ie = locations.end();
         it != ie; ++it) {
      (*it)->adjustOffsetBound(checkedAddress, bounds);
    }
  }
  target->setAsCore(reason);

  // Compute the direct pointer flow dependency
  std::map<ref<VersionedValue>, ref<MemoryLocation> > sources =
      target->getSources();

  for (std::map<ref<VersionedValue>, ref<MemoryLocation> >::iterator
           it = sources.begin(),
           ie = sources.end();
       it != ie; ++it) {
    markPointerFlow(it->first, checkedAddress, bounds, reason);
  }

  // We use normal marking with markFlow for load/store addresses
  markFlow(target->getLoadAddress(), reason);
  markFlow(target->getStoreAddress(), reason);
}

std::vector<ref<VersionedValue> > Dependency::populateArgumentValuesList(
    llvm::CallInst *site, const std::vector<llvm::Instruction *> &stack,
    std::vector<Cell> &arguments) {
  unsigned numArgs = site->getCalledFunction()->arg_size();
  std::vector<ref<VersionedValue> > argumentValuesList;
  for (unsigned i = numArgs; i > 0;) {
    llvm::Value *argOperand = site->getArgOperand(--i);
    ref<VersionedValue> latestValue = arguments.at(i).vvalue;

    if (!latestValue.isNull())
      argumentValuesList.push_back(latestValue);
    else {
      // This is for the case when latestValue was NULL, which means there is
      // no source dependency information for this node, e.g., a constant.
      argumentValuesList.push_back(
          VersionedValue::create(argOperand, stack, arguments[i].value));
    }
  }
  return argumentValuesList;
}

Dependency::Dependency(Dependency *parent, llvm::DataLayout *_targetData)
    : parent(parent), targetData(_targetData) {
  if (parent) {
    concretelyAddressedStore = parent->concretelyAddressedStore;
    symbolicallyAddressedStore = parent->symbolicallyAddressedStore;
    debugSubsumptionLevel = parent->debugSubsumptionLevel;
    debugState = parent->debugState;
  } else {
#ifdef ENABLE_Z3
    debugSubsumptionLevel = DebugSubsumption;
    debugState = DebugState;
#else
    debugSubsumptionLevel = 0;
    debugState = false;
#endif
  }
}

Dependency::~Dependency() {
  // Delete the locally-constructed relations
  concretelyAddressedStore.clear();
  symbolicallyAddressedStore.clear();

  // Delete valuesMap
  for (std::map<llvm::Value *, std::vector<ref<VersionedValue> > >::iterator
           it = valuesMap.begin(),
           ie = valuesMap.end();
       it != ie; ++it) {
    it->second.clear();
  }
  valuesMap.clear();
}

Dependency *Dependency::cdr() const { return parent; }

ref<VersionedValue>
Dependency::execute(llvm::Instruction *instr,
                    const std::vector<llvm::Instruction *> &stack,
                    std::vector<Cell> &args, bool symbolicExecutionError) {
  // The basic design principle that we need to be careful here
  // is that we should not store quadratic-sized structures in
  // the database of computed relations, e.g., not storing the
  // result of traversals of the graph. We keep the
  // quadratic blow up for only when querying the database.

  if (llvm::isa<llvm::CallInst>(instr)) {
    llvm::CallInst *callInst = llvm::dyn_cast<llvm::CallInst>(instr);
    llvm::Function *f = callInst->getCalledFunction();
    ref<VersionedValue> ret;

    if (!f) {
	// Handles the case when the callee is wrapped within another expression
	llvm::ConstantExpr *calledValue = llvm::dyn_cast<llvm::ConstantExpr>(callInst->getCalledValue());
	if (calledValue && calledValue->getOperand(0)) {
	    f = llvm::dyn_cast<llvm::Function>(calledValue->getOperand(0));
	}
    }

    if (f && f->getIntrinsicID() == llvm::Intrinsic::not_intrinsic) {
      llvm::StringRef calleeName = f->getName();
      // FIXME: We need a more precise way to determine invoked method
      // rather than just using the name.
      std::string getValuePrefix("klee_get_value");

      if (calleeName.equals("_Znwm") || calleeName.equals("_Znam")) {
        ConstantExpr *sizeExpr = llvm::dyn_cast<ConstantExpr>(args.at(1).value);
        ret = getNewPointerValue(instr, stack, args.at(0).value,
                                 sizeExpr->getZExtValue());
      } else if ((calleeName.equals("getpagesize") && args.size() == 1) ||
                 (calleeName.equals("ioctl") && args.size() == 4) ||
                 (calleeName.equals("__ctype_b_loc") && args.size() == 1) ||
                 (calleeName.equals("__ctype_b_locargs") && args.size() == 1) ||
                 calleeName.equals("puts") || calleeName.equals("fflush") ||
                 calleeName.equals("strcmp") || calleeName.equals("strncmp") ||
                 (calleeName.equals("__errno_location") && args.size() == 1) ||
                 (calleeName.equals("geteuid") && args.size() == 1)) {
        ret = getNewVersionedValue(instr, stack, args.at(0).value);
      } else if (calleeName.equals("_ZNSi5seekgElSt12_Ios_Seekdir") &&
                 args.size() == 4) {
        ret = getNewVersionedValue(instr, stack, args.at(0).value);
        for (unsigned i = 0; i < 3; ++i) {
          addDependencyViaExternalFunction(stack, args.at(i + 1).vvalue, ret);
        }
      } else if (calleeName.equals(
                     "_ZNSt13basic_fstreamIcSt11char_traitsIcEE7is_openEv") &&
                 args.size() == 2) {
        ret = getNewVersionedValue(instr, stack, args.at(0).value);
        addDependencyViaExternalFunction(stack, args.at(1).vvalue, ret);
      } else if (calleeName.equals("_ZNSi5tellgEv") && args.size() == 2) {
        ret = getNewVersionedValue(instr, stack, args.at(0).value);
        addDependencyViaExternalFunction(stack, args.at(1).vvalue, ret);
      } else if ((calleeName.equals("powl") && args.size() == 3) ||
                 (calleeName.equals("gettimeofday") && args.size() == 3)) {
        ret = getNewVersionedValue(instr, stack, args.at(0).value);
        for (unsigned i = 0; i < 2; ++i) {
          addDependencyViaExternalFunction(stack, args.at(i + 1).vvalue, ret);
        }
      } else if (calleeName.equals("malloc") && args.size() == 1) {
        // malloc is an location-type instruction. This is for the case when the
        // allocation size is unknown (0), so the
        // single argument here is the return address, for which KLEE provides
        // 0.
        ret = getNewPointerValue(instr, stack, args.at(0).value, 0);
      } else if (calleeName.equals("malloc") && args.size() == 2) {
        // malloc is an location-type instruction. This is the case when it has
        // a determined size
        uint64_t size = 0;
        if (ConstantExpr *ce = llvm::dyn_cast<ConstantExpr>(args.at(1).value))
          size = ce->getZExtValue();
        ret = getNewPointerValue(instr, stack, args.at(0).value, size);
      } else if (calleeName.equals("realloc") && args.size() == 1) {
        // realloc is an location-type instruction: its single argument is the
        // return address.
        ret = getNewVersionedValue(instr, stack, args.at(0).value);
        addDependency(args.at(0).vvalue, ret);
      } else if (calleeName.equals("calloc") && args.size() == 1) {
        // calloc is a location-type instruction: its single argument is the
        // return address. We assume its allocation size is unknown
        ret = getNewPointerValue(instr, stack, args.at(0).value, 0);
      } else if (calleeName.equals("syscall") && args.size() >= 2) {
        ret = getNewVersionedValue(instr, stack, args.at(0).value);
        for (unsigned i = 0; i + 1 < args.size(); ++i) {
          addDependencyViaExternalFunction(stack, args.at(i + 1).vvalue, ret);
        }
      } else if (std::mismatch(getValuePrefix.begin(), getValuePrefix.end(),
                               calleeName.begin()).first ==
                     getValuePrefix.end() &&
                 args.size() == 2) {
        ret = getNewVersionedValue(instr, stack, args.at(0).value);
        addDependencyViaExternalFunction(stack, args.at(1).vvalue, ret);
      } else if (calleeName.equals("getenv") && args.size() == 2) {
        // We assume getenv has unknown allocation size
        ret = getNewPointerValue(instr, stack, args.at(0).value, 0);
      } else if (calleeName.equals("printf") && args.size() >= 2) {
        ret = getNewVersionedValue(instr, stack, args.at(0).value);
        addDependencyViaExternalFunction(stack, args.at(1).vvalue, ret);
        for (unsigned i = 2, argsNum = args.size(); i < argsNum; ++i) {
          addDependencyViaExternalFunction(stack, args.at(i).vvalue, ret);
        }
      } else if (calleeName.equals("vprintf") && args.size() == 3) {
        ret = getNewVersionedValue(instr, stack, args.at(0).value);
        addDependencyViaExternalFunction(stack, args.at(1).vvalue, ret);
        addDependencyViaExternalFunction(stack, args.at(2).vvalue, ret);
      } else if (((calleeName.equals("fchmodat") && args.size() == 5)) ||
                 (calleeName.equals("fchownat") && args.size() == 6)) {
        ret = getNewVersionedValue(instr, stack, args.at(0).value);
        for (unsigned i = 0; i < 2; ++i) {
          addDependencyViaExternalFunction(stack, args.at(i + 1).vvalue, ret);
        }
      } else {
        // Default external function handler: We ignore functions that return
        // void, and we DO NOT build dependency of return value to the
        // arguments.
        if (!instr->getType()->isVoidTy()) {
          assert(args.size() && "non-void call missing return expression");
          klee_warning("using default handler for external function %s",
                       calleeName.str().c_str());
          ret = getNewVersionedValue(instr, stack, args.at(0).value);
        }
      }
    }
    return ret;
  }

  switch (args.size()) {
  case 0: {
    switch (instr->getOpcode()) {
    case llvm::Instruction::Br: {
      llvm::BranchInst *binst = llvm::dyn_cast<llvm::BranchInst>(instr);
      if (binst && binst->isConditional()) {
        ref<Expr> unknownExpression;
        std::string reason = "";
        if (debugSubsumptionLevel >= 1) {
          llvm::raw_string_ostream stream(reason);
          stream << "branch instruction [";
          if (binst->getParent()->getParent()) {
            stream << binst->getParent()->getParent()->getName().str() << ": ";
          }
          if (llvm::MDNode *n = binst->getMetadata("dbg")) {
            llvm::DILocation loc(n);
            stream << "Line " << loc.getLineNumber();
          } else {
            binst->print(stream);
          }
          stream << "]";
          stream.flush();
        }
        markAllValues(binst->getCondition(), unknownExpression, reason);
      }
      break;
    }
    default:
      break;
    }
    ref<VersionedValue> nullRet;
    return nullRet;
  }
  case 1: {
    Cell argCell = args.at(0);
    ref<VersionedValue> ret;

    switch (instr->getOpcode()) {
    case llvm::Instruction::BitCast: {

      if (!argCell.vvalue.isNull()) {
        ret = getNewVersionedValue(instr, stack, argCell.value);
        addDependency(argCell.vvalue, ret);
      } else if (!llvm::isa<llvm::Constant>(instr->getOperand(0)))
          // Constants would kill dependencies, the remaining is for
          // cases that may actually require dependencies.
      {
        if (instr->getOperand(0)->getType()->isPointerTy()) {
          uint64_t size = targetData->getTypeStoreSize(
              instr->getOperand(0)->getType()->getPointerElementType());
          ret = getNewVersionedValue(instr, stack, argCell.value);
          addDependency(getNewPointerValue(instr->getOperand(0), stack,
                                           argCell.value, size),
                        ret);
        } else if (llvm::isa<llvm::Argument>(instr->getOperand(0)) ||
                   llvm::isa<llvm::CallInst>(instr->getOperand(0)) ||
                   symbolicExecutionError) {
          ret = getNewVersionedValue(instr, stack, argCell.value);
          addDependency(
              getNewVersionedValue(instr->getOperand(0), stack, argCell.value),
              ret);
        } else {
          assert(!"operand not found");
        }
      }
      break;
    }
    default: { assert(!"unhandled unary instruction"); }
    }
    return ret;
  }
  case 2: {
    Cell valueCell = args.at(0);
    Cell address = args.at(1);
    ref<VersionedValue> ret;

    switch (instr->getOpcode()) {
    case llvm::Instruction::Alloca: {
      // In case of alloca, the valueCell is the address, and address is the
      // allocation size.
      uint64_t size = 0;
      if (ConstantExpr *ce = llvm::dyn_cast<ConstantExpr>(address.value)) {
        size = ce->getZExtValue();
      }
      ret = getNewPointerValue(instr, stack, valueCell.value, size);
      break;
    }
    case llvm::Instruction::Load: {
      llvm::Type *loadedType =
          instr->getOperand(0)->getType()->getPointerElementType();

      if (!address.vvalue.isNull()) {
        std::set<ref<MemoryLocation> > locations =
            address.vvalue->getLocations();
        if (locations.empty()) {
          // The size of the allocation is unknown here as the memory region
          // might have been allocated by the environment
          ref<MemoryLocation> loc = MemoryLocation::create(
              instr->getOperand(0), stack, address.value, 0);
          address.vvalue->addLocation(loc);

          // Build the loaded value
          ret = loadedType->isPointerTy()
                    ? getNewPointerValue(instr, stack, valueCell.value, 0)
                    : getNewVersionedValue(instr, stack, valueCell.value);

          updateStore(loc, address.vvalue, ret);
          break;
        } else if (locations.size() == 1) {
          ref<MemoryLocation> loc = *(locations.begin());
          if (isMainArgument(loc->getValue())) {
            // The load corresponding to a load of the main function's argument
            // that was never allocated within this program.

            // Build the loaded value
            ret = loadedType->isPointerTy()
                      ? getNewPointerValue(instr, stack, valueCell.value, 0)
                      : getNewVersionedValue(instr, stack, valueCell.value);

            updateStore(loc, address.vvalue, ret);
            break;
          }
        }
      } else {
        // assert(!"loaded allocation size must not be zero");
        ref<VersionedValue> addressValue =
            getNewPointerValue(instr->getOperand(0), stack, address.value, 0);

        if (llvm::isa<llvm::GlobalVariable>(instr->getOperand(0))) {
          // The value not found was a global variable, record it here.
          std::set<ref<MemoryLocation> > locations =
              addressValue->getLocations();

          // Build the loaded value
          ret = loadedType->isPointerTy()
                    ? getNewPointerValue(instr, stack, valueCell.value, 0)
                    : getNewVersionedValue(instr, stack, valueCell.value);

          updateStore(*(locations.begin()), addressValue, ret);
          break;
        }
      }

      std::set<ref<MemoryLocation> > locations = address.vvalue->getLocations();

      for (std::set<ref<MemoryLocation> >::iterator li = locations.begin(),
                                                    le = locations.end();
           li != le; ++li) {
        std::pair<ref<VersionedValue>, ref<VersionedValue> > addressValuePair;

        if ((*li)->hasConstantAddress()) {
          if (concretelyAddressedStore.count(*li) > 0) {
            addressValuePair = concretelyAddressedStore[*li];
          }
        } else if (symbolicallyAddressedStore.count(*li) > 0) {
          // FIXME: Here we assume that the expressions have to exactly be the
          // same expression object. More properly, this should instead add an
          // ite constraint onto the path condition.
          addressValuePair = concretelyAddressedStore[*li];
        }

        // Build the loaded value
        ret = (addressValuePair.second.isNull() ||
               addressValuePair.second->getLocations().empty()) &&
                      loadedType->isPointerTy()
                  ? getNewPointerValue(instr, stack, valueCell.value, 0)
                  : getNewVersionedValue(instr, stack, valueCell.value);

        if (addressValuePair.second.isNull() ||
            ret->getExpression() != addressValuePair.second->getExpression()) {
          // We could not find the stored value, create a new one.
          updateStore(*li, address.vvalue, ret);
          ret->setLoadAddress(address.vvalue);
        } else {
          addDependencyViaLocation(addressValuePair.second, ret, *li);
          ret->setLoadAddress(address.vvalue);
          ret->setStoreAddress(addressValuePair.first);
        }
      }
      break;
    }
    case llvm::Instruction::Store: {
      // If there was no dependency found, we should create
      // a new value
      ref<VersionedValue> storedValue = valueCell.vvalue;
      ref<VersionedValue> addressValue = address.vvalue;

      if (storedValue.isNull())
        storedValue =
            getNewVersionedValue(instr->getOperand(0), stack, valueCell.value);

      if (addressValue.isNull()) {
        // assert(!"null address");
        addressValue =
            getNewPointerValue(instr->getOperand(1), stack, address.value, 0);
      } else if (address.vvalue->getLocations().size() == 0) {
        if (instr->getOperand(1)->getType()->isPointerTy()) {
          addressValue->addLocation(MemoryLocation::create(
              instr->getOperand(1), stack, address.value, 0));
        } else {
          assert(!"address is not a pointer");
        }
      }

      std::set<ref<MemoryLocation> > locations = addressValue->getLocations();

      for (std::set<ref<MemoryLocation> >::iterator it = locations.begin(),
                                                    ie = locations.end();
           it != ie; ++it) {
        updateStore(*it, addressValue, storedValue);
      }
      break;
    }
    case llvm::Instruction::Trunc:
    case llvm::Instruction::ZExt:
    case llvm::Instruction::FPTrunc:
    case llvm::Instruction::FPExt:
    case llvm::Instruction::FPToUI:
    case llvm::Instruction::FPToSI:
    case llvm::Instruction::UIToFP:
    case llvm::Instruction::SIToFP:
    case llvm::Instruction::IntToPtr:
    case llvm::Instruction::PtrToInt:
    case llvm::Instruction::SExt:
    case llvm::Instruction::ExtractValue: {
      Cell result = args.at(0);
      Cell argCell = args.at(1);

      if (!argCell.vvalue.isNull()) {
        if (llvm::isa<llvm::IntToPtrInst>(instr)) {
          if (argCell.vvalue->getLocations().size() == 0) {
            ret = getNewPointerValue(instr, stack, result.value, 0);
            // 0 signifies unknown allocation size
            addDependencyToNonPointer(argCell.vvalue, ret);
          } else {
            ret = getNewVersionedValue(instr, stack, result.value);
            addDependencyIntToPtr(argCell.vvalue, ret);
          }
        } else {
          ret = getNewVersionedValue(instr, stack, result.value);
          addDependency(argCell.vvalue, ret);
        }
      } else if (!llvm::isa<llvm::Constant>(instr->getOperand(0)))
          // Constants would kill dependencies, the remaining is for
          // cases that may actually require dependencies.
      {
        if (instr->getOperand(0)->getType()->isPointerTy()) {
          uint64_t size = targetData->getTypeStoreSize(
              instr->getOperand(0)->getType()->getPointerElementType());
          ret = getNewVersionedValue(instr, stack, result.value);
          // Here we create normal non-pointer value for the
          // dependency target as it will be properly made a
          // pointer value by addDependency.
          addDependency(getNewPointerValue(instr->getOperand(0), stack,
                                           argCell.value, size),
                        ret);
        } else if (llvm::isa<llvm::Argument>(instr->getOperand(0)) ||
                   llvm::isa<llvm::CallInst>(instr->getOperand(0)) ||
                   symbolicExecutionError) {
          if (llvm::isa<llvm::IntToPtrInst>(instr)) {
            ret = getNewPointerValue(instr, stack, result.value, 0);
            // 0 signifies unknown allocation size
            addDependency(getNewVersionedValue(instr->getOperand(0), stack,
                                               argCell.value),
                          ret);
          } else {
            ret = getNewVersionedValue(instr, stack, result.value);
            addDependency(getNewVersionedValue(instr->getOperand(0), stack,
                                               argCell.value),
                          ret);
          }
        } else {
          assert(!"operand not found");
        }
      }
      break;
    }
    default: { assert(!"unhandled binary instruction"); }
    }
    return ret;
  }
  case 3: {
    Cell result = args.at(0);
    Cell op1Cell = args.at(1);
    Cell op2Cell = args.at(2);
    ref<VersionedValue> ret;

    switch (instr->getOpcode()) {
    case llvm::Instruction::Select: {
      ret = getNewVersionedValue(instr, stack, result.value);

      if (result.value == op1Cell.value) {
        addDependency(op1Cell.vvalue, ret);
      } else if (result.value == op2Cell.value) {
        addDependency(op2Cell.vvalue, ret);
      } else {
        addDependency(op1Cell.vvalue, ret);
        // We do not require that the locations set is empty
        addDependency(op2Cell.vvalue, ret, false);
      }
      break;
    }

    case llvm::Instruction::Add:
    case llvm::Instruction::Sub:
    case llvm::Instruction::Mul:
    case llvm::Instruction::UDiv:
    case llvm::Instruction::SDiv:
    case llvm::Instruction::URem:
    case llvm::Instruction::SRem:
    case llvm::Instruction::And:
    case llvm::Instruction::Or:
    case llvm::Instruction::Xor:
    case llvm::Instruction::Shl:
    case llvm::Instruction::LShr:
    case llvm::Instruction::AShr:
    case llvm::Instruction::ICmp:
    case llvm::Instruction::FAdd:
    case llvm::Instruction::FSub:
    case llvm::Instruction::FMul:
    case llvm::Instruction::FDiv:
    case llvm::Instruction::FRem:
    case llvm::Instruction::FCmp:
    case llvm::Instruction::InsertValue: {
      ref<VersionedValue> op1 = op1Cell.vvalue;
      ref<VersionedValue> op2 = op2Cell.vvalue;

      if (op1.isNull() &&
          (instr->getParent()->getParent()->getName().equals("klee_range") &&
           instr->getOperand(0)->getName().equals("start"))) {
        op1 = getNewVersionedValue(instr->getOperand(0), stack, op1Cell.value);
      }
      if (op2.isNull() &&
          (instr->getParent()->getParent()->getName().equals("klee_range") &&
           instr->getOperand(1)->getName().equals("end"))) {
        op2 = getNewVersionedValue(instr->getOperand(1), stack, op2Cell.value);
      }

      if (!op1.isNull() || !op2.isNull()) {
        ret = getNewVersionedValue(instr, stack, result.value);
        if (instr->getOpcode() == llvm::Instruction::ICmp ||
            instr->getOpcode() == llvm::Instruction::FCmp) {
          addDependencyToNonPointer(op1, ret);
          addDependencyToNonPointer(op2, ret);
        } else {
          addDependency(op1, ret);
          // We do not require that the locations set is empty
          addDependency(op2, ret, false);
        }
      }
      break;
    }
    case llvm::Instruction::GetElementPtr: {
      Cell resultAddress = args.at(0);
      Cell inputAddress = args.at(1);
      Cell inputOffset = args.at(2);

      ref<VersionedValue> ret =
          getNewVersionedValue(instr, stack, resultAddress.value);

      ref<VersionedValue> addressValue = inputAddress.vvalue;
      if (addressValue.isNull()) {
        // assert(!"null address");
        addressValue = getNewPointerValue(instr->getOperand(0), stack,
                                          inputAddress.value, 0);
      } else if (addressValue->getLocations().size() == 0) {
        // Note that the allocation has unknown size here (0).
        addressValue->addLocation(MemoryLocation::create(
            instr->getOperand(0), stack, inputAddress.value, 0));
      }

      addDependencyWithOffset(addressValue, ret, inputOffset.value);
      break;
    }
    default:
      assert(!"unhandled ternary instruction");
    }
    return ret;
  }
  default:
    break;
  }
  assert(!"unhandled instruction arguments number");
}

ref<VersionedValue>
Dependency::executePHI(llvm::Instruction *instr, unsigned int incomingBlock,
                       const std::vector<llvm::Instruction *> &stack,
                       Cell valueCell, bool symbolicExecutionError) {
  llvm::PHINode *node = llvm::dyn_cast<llvm::PHINode>(instr);
  llvm::Value *llvmArgValue = node->getIncomingValue(incomingBlock);
  ref<VersionedValue> val = valueCell.vvalue;
  if (!val.isNull()) {
    addDependency(val, getNewVersionedValue(instr, stack, valueCell.value));
  } else if (llvm::isa<llvm::Constant>(llvmArgValue) ||
             llvm::isa<llvm::Argument>(llvmArgValue) ||
             symbolicExecutionError) {
    getNewVersionedValue(instr, stack, valueCell.value);
  } else {
    assert(!"operand not found");
  }
  return val;
}

ref<VersionedValue> Dependency::executeMemoryOperation(
    llvm::Instruction *instr, const std::vector<llvm::Instruction *> &stack,
    std::vector<Cell> &args, bool boundsCheck, bool symbolicExecutionError) {
  ref<VersionedValue> ret = execute(instr, stack, args, symbolicExecutionError);
#ifdef ENABLE_Z3
  if (!NoBoundInterpolation && boundsCheck) {
    // The bounds check has been proven valid, we keep the dependency on the
    // address. Calling va_start within a variadic function also triggers memory
    // operation, but we ignored it here as this method is only called when load
    // / store instruction is processed.
    llvm::Value *addressOperand;
    ref<Expr> address(args.at(1).value);
    switch (instr->getOpcode()) {
    case llvm::Instruction::Load: {
      addressOperand = instr->getOperand(0);
      break;
    }
    case llvm::Instruction::Store: {
      addressOperand = instr->getOperand(1);
      break;
    }
    default: {
      assert(!"unknown memory operation");
      break;
    }
    }

    if (SpecialFunctionBoundInterpolation) {
      // Limit interpolation to only within function tracerx_check
      ref<VersionedValue> val(
          getLatestValueForMarking(addressOperand, address));
      if (llvm::isa<llvm::LoadInst>(instr) && !val->getLocations().empty()) {
        if (instr->getParent()->getParent()->getName().str() ==
            "tracerx_check") {
          std::set<ref<MemoryLocation> > locations(val->getLocations());
          for (std::set<ref<MemoryLocation> >::iterator it = locations.begin(),
                                                        ie = locations.end();
               it != ie; ++it) {
            if (llvm::ConstantExpr *ce =
                    llvm::dyn_cast<llvm::ConstantExpr>((*it)->getValue())) {
              if (llvm::isa<llvm::GetElementPtrInst>(ce->getAsInstruction())) {
                std::string reason = "";
                if (debugSubsumptionLevel >= 1) {
                  llvm::raw_string_ostream stream(reason);
                  stream << "pointer use [";
                  if (instr->getParent()->getParent()) {
                    stream << instr->getParent()->getParent()->getName().str()
                           << ": ";
                  }
                  if (llvm::MDNode *n = instr->getMetadata("dbg")) {
                    llvm::DILocation loc(n);
                    stream << "Line " << loc.getLineNumber();
                  }
                  stream << "]";
                  stream.flush();
                }
                if (ExactAddressInterpolant) {
                  markAllValues(addressOperand, address, reason);
                } else {
                  markAllPointerValues(addressOperand, address, reason);
                }
                break;
              }
            }
          }
        }
      }
    } else {
      std::string reason = "";
      if (debugSubsumptionLevel >= 1) {
        llvm::raw_string_ostream stream(reason);
        stream << "pointer use [";
        if (instr->getParent()->getParent()) {
          stream << instr->getParent()->getParent()->getName().str() << ": ";
        }
        if (llvm::MDNode *n = instr->getMetadata("dbg")) {
          llvm::DILocation loc(n);
          stream << "Line " << loc.getLineNumber();
        }
        stream << "]";
        stream.flush();
      }
      if (ExactAddressInterpolant) {
        markAllValues(addressOperand, address, reason);
      } else {
        markAllPointerValues(addressOperand, address, reason);
      }
    }
  }
#endif
  return ret;
}

void Dependency::bindCallArguments(llvm::Instruction *i,
                                   std::vector<llvm::Instruction *> &stack,
                                   std::vector<Cell> &arguments) {
  llvm::CallInst *site = llvm::dyn_cast<llvm::CallInst>(i);

  if (!site)
    return;

  llvm::Function *callee = site->getCalledFunction();

  // Sometimes the callee information is missing, in which case
  // the callee is not to be symbolically tracked.
  if (!callee)
    return;

  argumentValuesList = populateArgumentValuesList(site, stack, arguments);

  unsigned index = 0;
  stack.push_back(i);
  for (llvm::Function::ArgumentListType::iterator
           it = callee->getArgumentList().begin(),
           ie = callee->getArgumentList().end();
       it != ie; ++it) {
    if (!argumentValuesList.back().isNull()) {

      addDependency(argumentValuesList.back(),
                    getNewVersionedValue(
                        it, stack, argumentValuesList.back()->getExpression()));
    }
    argumentValuesList.pop_back();
    ++index;
  }
}

void Dependency::bindReturnValue(llvm::CallInst *site,
                                 std::vector<llvm::Instruction *> &stack,
                                 llvm::Instruction *i, Cell returnCell) {
  llvm::ReturnInst *retInst = llvm::dyn_cast<llvm::ReturnInst>(i);
  if (site && retInst &&
      retInst->getReturnValue() // For functions returning void
      ) {
    ref<VersionedValue> value = returnCell.vvalue;
    if (!stack.empty()) {
      stack.pop_back();
    }
    if (!value.isNull())
      addDependency(value, getNewVersionedValue(site, stack, returnCell.value));
  }
}

void Dependency::markAllValues(ref<VersionedValue> value,
                               const std::string &reason) {
  markFlow(value, reason);
}

void Dependency::markAllValues(llvm::Value *val, ref<Expr> expr,
                               const std::string &reason) {
  ref<VersionedValue> value = getLatestValueForMarking(val, expr);

  if (value.isNull())
    return;

  markFlow(value, reason);
}

void Dependency::markAllPointerValues(llvm::Value *val, ref<Expr> address,
                                      std::set<ref<Expr> > &bounds,
                                      const std::string &reason) {
  ref<VersionedValue> value = getLatestValueForMarking(val, address);

  if (value.isNull())
    return;

  markPointerFlow(value, value, bounds, reason);
}

void Dependency::print(llvm::raw_ostream &stream) const {
  this->print(stream, 0);
}

void Dependency::print(llvm::raw_ostream &stream,
                       const unsigned paddingAmount) const {
  std::string tabs = makeTabs(paddingAmount);
  std::string tabsNext = appendTab(tabs);
  std::string tabsNextNext = appendTab(tabsNext);

  if (concretelyAddressedStore.empty()) {
    stream << tabs << "concrete store = []\n";
  } else {
    stream << tabs << "concrete store = [\n";
    for (std::map<ref<MemoryLocation>,
                  std::pair<ref<VersionedValue>,
                            ref<VersionedValue> > >::const_iterator
             is = concretelyAddressedStore.begin(),
             ie = concretelyAddressedStore.end(), it = is;
         it != ie; ++it) {
      if (it != is)
        stream << tabsNext << "------------------------------------------\n";
      stream << tabsNext << "address:\n";
      it->first->print(stream, tabsNextNext);
      stream << "\n";
      stream << tabsNext << "content:\n";
      it->second.second->print(stream, tabsNextNext);
      stream << "\n";
    }
    stream << tabs << "]\n";
  }

  if (symbolicallyAddressedStore.empty()) {
    stream << tabs << "symbolic store = []\n";
  } else {
    stream << tabs << "symbolic store = [\n";
    for (std::map<ref<MemoryLocation>,
                  std::pair<ref<VersionedValue>,
                            ref<VersionedValue> > >::const_iterator
             is = symbolicallyAddressedStore.begin(),
             ie = symbolicallyAddressedStore.end(), it = is;
         it != ie; ++it) {
      if (it != is)
        stream << tabsNext << "------------------------------------------\n";
      stream << tabsNext << "address:\n";
      it->first->print(stream, tabsNextNext);
      stream << "\n";
      stream << tabsNext << "content:\n";
      it->second.second->print(stream, tabsNextNext);
      stream << "\n";
    }
    stream << "]\n";
  }

  if (parent) {
    stream << tabs << "--------- Parent Dependencies ----------\n";
    parent->print(stream, paddingAmount);
  }
}

}
