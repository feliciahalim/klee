//===-- TxStore.cpp - A view of program memory ------------------*- C++ -*-===//
//
//               The Tracer-X KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// This file contains the implementations of the shadow memory to support the
/// dependency computation of memory locations and the generation of
/// interpolants.
///
//===----------------------------------------------------------------------===//

#include "TxStore.h"

#include "klee/CommandLine.h"
#include "klee/Internal/Module/TxValues.h"
#include "klee/util/TxPrintUtil.h"

using namespace klee;

namespace klee {

ref<TxStoreEntry>
TxStore::MiddleStateStore::find(ref<TxStateAddress> loc) const {
  ref<TxStoreEntry> ret;

  if (loc->hasConstantAddress()) {
    TxStore::LowerStateStore::const_iterator lowerStoreIter =
        concretelyAddressedStore.find(loc->getAsVariable());

    if (lowerStoreIter != concretelyAddressedStore.end()) {
      ret = lowerStoreIter->second;
    }
  } else {
    TxStore::LowerStateStore::const_iterator lowerStoreIter =
        symbolicallyAddressedStore.find(loc->getAsVariable());
    if (lowerStoreIter != symbolicallyAddressedStore.end()) {
      ret = lowerStoreIter->second;
    }
  }

  return ret;
}

ref<TxStoreEntry>
TxStore::MiddleStateStore::find(ref<TxAllocationContext> alc) const {
  ref<TxStoreEntry> ret;

  for (LowerStateStore::const_iterator
           lowerIs = concretelyAddressedStore.begin(),
           lowerIe = concretelyAddressedStore.end(), lowerIt = lowerIs;
       lowerIt != lowerIe; ++lowerIt) {
    if (lowerIt->first->getAllocationInfo()->getContext() == alc)
      return lowerIt->second;
  }

  for (LowerStateStore::const_iterator
           lowerIs = symbolicallyAddressedStore.begin(),
           lowerIe = symbolicallyAddressedStore.end(), lowerIt = lowerIs;
       lowerIt != lowerIe; ++lowerIt) {
    if (lowerIt->first->getAllocationInfo()->getContext() == alc)
      return lowerIt->second;
  }

  return ret;
}

ref<TxStoreEntry> TxStore::MiddleStateStore::findConcrete(
    ref<TxVariable> var,
    std::map<ref<TxAllocationInfo>, ref<TxAllocationInfo> > &unifiedBases)
    const {
  ref<TxStoreEntry> ret;
  TxStore::LowerStateStore::const_iterator lowerStoreIter =
      concretelyAddressedStore.find(var);
  if (lowerStoreIter != concretelyAddressedStore.end()) {
    ret = lowerStoreIter->second;
  } else {
    for (TxStore::LowerStateStore::const_iterator
             it = concretelyAddressedStore.begin(),
             ie = concretelyAddressedStore.end();
         it != ie; ++it) {
      if (it->first->getOffset() == var->getOffset()) {
        if (it->first->getAllocationInfo()->translate(var->getAllocationInfo(),
                                                      unifiedBases)) {
          ret = it->second;
        }
        break;
      }
    }
  }
  return ret;
}

ref<TxStoreEntry>
TxStore::MiddleStateStore::findSymbolic(ref<TxVariable> var) const {
  ref<TxStoreEntry> ret;
  TxStore::LowerStateStore::const_iterator lowerStoreIter =
      symbolicallyAddressedStore.find(var);
  if (lowerStoreIter != symbolicallyAddressedStore.end()) {
    ret = lowerStoreIter->second;
  }
  return ret;
}

ref<TxStoreEntry> TxStore::MiddleStateStore::updateStore(
    const TxStore *store, ref<TxStateAddress> loc, ref<TxStateValue> address,
    ref<TxStateValue> value, uint64_t _depth) {
  ref<TxStoreEntry> ret;

  // Return null entry in case allocation info do not match
  if (loc->getAllocationInfo() != allocInfo)
    return ret;

  ret = ref<TxStoreEntry>(new TxStoreEntry(loc, address, value, store, _depth));
  if (loc->hasConstantAddress()) {
    concretelyAddressedStore[loc->getAsVariable()] = ret;
  } else {
    symbolicallyAddressedStore[loc->getAsVariable()] = ret;
  }
  return ret;
}

void TxStore::MiddleStateStore::print(llvm::raw_ostream &stream,
                                      const std::string &prefix) const {
  std::string tabsNext = appendTab(prefix);
  std::string tabsNextNext = appendTab(tabsNext);

  allocInfo->print(stream, prefix);
  stream << ":";
  stream << "\n" << prefix << "concretely-addressed store = [";
  if (!concretelyAddressedStore.empty()) {
    stream << "\n";
    for (LowerStateStore::const_iterator
             lowerIs = concretelyAddressedStore.begin(),
             lowerIe = concretelyAddressedStore.end(), lowerIt = lowerIs;
         lowerIt != lowerIe; ++lowerIt) {
      if (lowerIt != lowerIs)
        stream << tabsNext << "------------------------------------------\n";
      stream << tabsNext << "address:\n";
      lowerIt->second->getAddress()->print(stream, tabsNextNext);
      stream << "\n";
      stream << tabsNext << "content:\n";
      lowerIt->second->getContent()->print(stream, tabsNextNext);
      stream << "\n";
    }
    stream << prefix;
  }
  stream << "]";

  stream << "\n" << prefix << "symbolically-addressed store = [";
  if (!symbolicallyAddressedStore.empty()) {
    stream << "\n";
    for (LowerStateStore::const_iterator
             lowerIs = symbolicallyAddressedStore.begin(),
             lowerIe = symbolicallyAddressedStore.end(), lowerIt = lowerIs;
         lowerIt != lowerIe; ++lowerIt) {
      if (lowerIt != lowerIs)
        stream << tabsNext << "------------------------------------------\n";
      stream << tabsNext << "address:\n";
      lowerIt->second->getAddress()->print(stream, tabsNextNext);
      stream << "\n";
      stream << tabsNext << "content:\n";
      lowerIt->second->getContent()->print(stream, tabsNextNext);
      stream << "\n";
    }
    stream << prefix;
  }
  stream << "]";
}

/**/

bool TxStore::isInLeftSubtree(uint64_t targetDepth) const {
  const TxStore *current = this;
  bool inLeftSubtree = false;

  if (current->depth == targetDepth)
    return false;

  assert(current->depth > targetDepth &&
         "entry should have been defined in an ancestor node");

  while (current->depth > targetDepth) {
    if (current == current->parent->left) {
      inLeftSubtree = true;
    } else {
      inLeftSubtree = false;
    }
    current = current->parent;
  }

  return inLeftSubtree;
}

bool TxStore::adjustOffsetBound(ref<TxStoreEntry> entry, bool leftMarking,
                                ref<TxStateValue> checkedAddress,
                                std::set<uint64_t> &bounds,
                                const std::string &reason, bool &boundUpdated) {
  bool memoryError = false;
  if (entry->canInterpolateBound(leftMarking)) {
    memoryError = entry->getPointerInfo(leftMarking)
                      ->adjustOffsetBound(checkedAddress, bounds, boundUpdated);
  }

  // If this was the first time this value gets marked, we should propagate the
  // marking further
  if (!entry->isCore(leftMarking))
    boundUpdated = true;

  entry->setAsCore(leftMarking, reason);

  return memoryError;
}

ref<TxStoreEntry> TxStore::find(ref<TxStateAddress> loc) const {
  TopStateStore::const_iterator storeIter =
      internalStore.find(loc->getContext());
  if (storeIter != internalStore.end()) {
    return storeIter->second.find(loc);
  }

  ref<TxStoreEntry> nullEntry;
  return nullEntry;
}

ref<TxStoreEntry> TxStore::find(ref<TxAllocationContext> alc) const {
  TopStateStore::const_iterator storeIter = internalStore.find(alc);
  if (storeIter != internalStore.end()) {
    return storeIter->second.find(alc);
  }

  ref<TxStoreEntry> nullEntry;
  return nullEntry;
}

ref<TxStoreEntry> TxStore::find(ref<TxAllocationContext> alc,
                                ref<Expr> offset) const {
  assert(isa<ConstantExpr>(offset) &&
         "TxStore::find, offset is not a constant value");
  TopStateStore::const_iterator storeIter = internalStore.find(alc);
  if (storeIter != internalStore.end()) {
    MiddleStateStore array = storeIter->second;
    for (LowerStateStore::const_iterator it = array.concreteBegin(),
                                         ie = array.concreteEnd();
         it != ie; ++it) {
      ref<TxStoreEntry> tmp = (*it).second;
      if (offset.compare(tmp->getIndex()->getOffset()) == 0)
        return tmp;
    }
    for (LowerStateStore::const_iterator it = array.symbolicBegin(),
                                         ie = array.symbolicBegin();
         it != ie; ++it) {
      ref<TxStoreEntry> tmp = (*it).second;
      if (offset.compare(tmp->getIndex()->getOffset()) == 0)
        return tmp;
    }
  }
  ref<TxStoreEntry> nullEntry;
  return nullEntry;
}

void TxStore::getStoredExpressions(
    const TxStore *referenceStore,
    const std::vector<llvm::Instruction *> &callHistory,
    const std::map<ref<Expr>, ref<Expr> > &substitution,
    std::set<const Array *> &replacements, bool coreOnly, bool leftRetrieval,
    TopStateStore &__internalStore,
    LowerStateStore &__concretelyAddressedHistoricalStore,
    LowerStateStore &__symbolicallyAddressedHistoricalStore) const {
  __internalStore = internalStore;
  __concretelyAddressedHistoricalStore = concretelyAddressedHistoricalStore;
  __symbolicallyAddressedHistoricalStore = symbolicallyAddressedHistoricalStore;
}

void TxStore::getStoredCoreExpressions(
    const TxStore *referenceStore,
    const std::vector<llvm::Instruction *> &callHistory,
    const std::map<ref<Expr>, ref<Expr> > &substitution,
    std::set<const Array *> &replacements, bool coreOnly, bool leftRetrieval,
    TopInterpolantStore &_concretelyAddressedStore,
    TopInterpolantStore &_symbolicallyAddressedStore,
    LowerInterpolantStore &_concretelyAddressedHistoricalStore,
    LowerInterpolantStore &_symbolicallyAddressedHistoricalStore) const {
  getConcreteStore(referenceStore, callHistory, substitution, replacements,
                   coreOnly, leftRetrieval, _concretelyAddressedStore,
                   _concretelyAddressedHistoricalStore);
  getSymbolicStore(referenceStore, callHistory, substitution, replacements,
                   coreOnly, leftRetrieval, _symbolicallyAddressedStore,
                   _symbolicallyAddressedHistoricalStore);
}

ref<TxAllocationContext>
TxStore::getAddressofLatestCopyLLVMValue(llvm::Value *val) {
  ref<TxAllocationContext> address;
  bool foundValue = false;
  for (TopStateStore::const_iterator it = internalStore.begin(),
                                     ie = internalStore.end();
       it != ie; ++it) {
    ref<TxAllocationContext> temp = (*it).first;
    if (temp->getValue()->getName() == val->getName()) {
      if (!foundValue) {
        address = temp;
        foundValue = true;
      } else if (temp->getCallHistory().size() >
                 address->getCallHistory().size()) {
        address = temp;
      }
    }
  }

  // Maybe NULL
  return address;
}

inline void TxStore::concreteToInterpolant(
    ref<TxVariable> variable, ref<TxStoreEntry> entry,
    const std::map<ref<Expr>, ref<Expr> > &substitution,
    std::set<const Array *> &replacements, bool coreOnly,
    LowerInterpolantStore &map, bool leftOfEntry) const {
  if (!coreOnly) {
    ref<TxInterpolantValue> interpolantValue =
        entry->getInterpolantStyleValue(leftOfEntry);
    map[variable] = interpolantValue;
  } else if (entry->isCore(leftOfEntry)) {
    // Do not add to the map if entry is not used
    // The reason for commenting this code and adding the if statement
    // after the commented code is to fix a bug which arises from
    // insertions in usedByLeftPath and usedByRightPath. An entry is
    // added to these if it is used in the subtree beneath it.
    // However, in some cases for example when a path is infeasible
    // the logic doesn't work. I have disabled this and I check both
    // paths.
    /*if (leftOfEntry) {
      if (usedByLeftPath.find(entry) == usedByLeftPath.end())
        return;
    } else if (usedByRightPath.find(entry) == usedByRightPath.end()) {
      return;
    }*/
    if (usedByLeftPath.find(entry) == usedByLeftPath.end() &&
        usedByRightPath.find(entry) == usedByRightPath.end())
      return;

// An address is in the core if it stores a value that is in the core
#ifdef ENABLE_Z3
    if (!NoExistential) {
      map[variable] =
          entry->getInterpolantValue(leftOfEntry, substitution, replacements);
    } else {
      map[variable] = entry->getInterpolantValue(leftOfEntry);
    }
#else
    map[variable] =
        entry->getInterpolantValue(leftOfEntry, substitution, replacements);
#endif
  }
}

inline void TxStore::symbolicToInterpolant(
    ref<TxVariable> variable, ref<TxStoreEntry> entry,
    const std::map<ref<Expr>, ref<Expr> > &substitution,
    std::set<const Array *> &replacements, bool coreOnly,
    LowerInterpolantStore &map, bool leftOfEntry) const {
  if (!coreOnly) {
    ref<TxInterpolantValue> interpolantValue =
        entry->getInterpolantStyleValue(leftOfEntry);
    map[variable] = interpolantValue;
  } else if (entry->isCore(leftOfEntry)) {
    // Do not add to the map if entry is not used
    // The reason for commenting this code and adding the if statement
    // after the commented code is to fix a bug which arises from
    // insertions in usedByLeftPath and usedByRightPath. An entry is
    // added to these if it is used in the subtree beneath it.
    // However, in some cases for example when a path is infeasible
    // the logic doesn't work. I have disabled this and I check both
    // paths.
    /*if (leftOfEntry) {
      if (usedByLeftPath.find(entry) == usedByLeftPath.end())
        return;
    } else if (usedByRightPath.find(entry) == usedByRightPath.end()) {
      return;
    }*/
    if (usedByRightPath.find(entry) == usedByRightPath.end() &&
        usedByLeftPath.find(entry) == usedByLeftPath.end())
      return;

// An address is in the core if it stores a value that is in the core
#ifdef ENABLE_Z3
    if (!NoExistential) {
      ref<TxVariable> address = TxStateAddress::create(
          entry->getAddress(), replacements)->getAsVariable();
      map[address] =
          entry->getInterpolantValue(leftOfEntry, substitution, replacements);
    } else {
      map[variable] = entry->getInterpolantValue(leftOfEntry);
    }
#else
    ref<TxVariable> address = TxStateAddress::create(
        entry->getAddress(), replacements)->getAsVariable();
    map[address] =
        entry->getInterpolantValue(leftOfEntry, substitution, replacements);
#endif
  }
}

void TxStore::getConcreteStore(
    const TxStore *referenceStore,
    const std::vector<llvm::Instruction *> &callHistory,
    const std::map<ref<Expr>, ref<Expr> > &substitution,
    std::set<const Array *> &replacements, bool coreOnly, bool leftRetrieval,
    TopInterpolantStore &_concretelyAddressedStore,
    LowerInterpolantStore &_concretelyAddressedHistoricalStore) const {
  for (TopStateStore::const_iterator it = internalStore.begin(),
                                     ie = internalStore.end();
       it != ie; ++it) {
    TopInterpolantStore::iterator storeIter =
        _concretelyAddressedStore.find(it->first);

    const MiddleStateStore &middleStore = it->second;

    if (storeIter == _concretelyAddressedStore.end()) {
      LowerInterpolantStore map;

      for (LowerStateStore::const_iterator it1 = middleStore.concreteBegin(),
                                           ie1 = middleStore.concreteEnd();
           it1 != ie1; ++it1) {
        concreteToInterpolant(
            it1->first, it1->second, substitution, replacements, coreOnly, map,
            referenceStore->isInLeftSubtree(it1->second->getDepth()));
      }

      // The map is only added when it is not empty; this is to avoid entries
      // mapped to empty structure in concretelyAddressedStore
      if (!map.empty()) {
        _concretelyAddressedStore[it->first] = map;
      }
    } else {
      for (LowerStateStore::const_iterator it1 = middleStore.concreteBegin(),
                                           ie1 = middleStore.concreteEnd();
           it1 != ie1; ++it1) {
        concreteToInterpolant(
            it1->first, it1->second, substitution, replacements, coreOnly,
            storeIter->second,
            referenceStore->isInLeftSubtree(it1->second->getDepth()));
      }
    }
  }

  for (LowerStateStore::const_iterator
           it = concretelyAddressedHistoricalStore.begin(),
           ie = concretelyAddressedHistoricalStore.end();
       it != ie; ++it) {

    concreteToInterpolant(
        it->first, it->second, substitution, replacements, coreOnly,
        _concretelyAddressedHistoricalStore,
        referenceStore->isInLeftSubtree(it->second->getDepth()));
  }
}

void TxStore::getSymbolicStore(
    const TxStore *referenceStore,
    const std::vector<llvm::Instruction *> &callHistory,
    const std::map<ref<Expr>, ref<Expr> > &substitution,
    std::set<const Array *> &replacements, bool coreOnly, bool leftRetrieval,
    TopInterpolantStore &_symbolicallyAddressedStore,
    LowerInterpolantStore &_symbolicallyAddressedHistoricalStore) const {
  for (TopStateStore::const_iterator it = internalStore.begin(),
                                     ie = internalStore.end();
       it != ie; ++it) {
    TopInterpolantStore::iterator storeIter =
        _symbolicallyAddressedStore.find(it->first);

    const MiddleStateStore &middleStore = it->second;

    if (storeIter == _symbolicallyAddressedStore.end()) {
      LowerInterpolantStore map;

      for (LowerStateStore::const_iterator it1 = middleStore.symbolicBegin(),
                                           ie1 = middleStore.symbolicEnd();
           it1 != ie1; ++it1) {
        symbolicToInterpolant(
            it1->first, it1->second, substitution, replacements, coreOnly, map,
            referenceStore->isInLeftSubtree(it1->second->getDepth()));
      }

      // The map is only added when it is not empty; this is to avoid entries
      // mapped to empty structure in symbolicallyAddressedStore
      if (!map.empty()) {
        _symbolicallyAddressedStore[it->first] = map;
      }
    } else {
      for (LowerStateStore::const_iterator it1 = middleStore.symbolicBegin(),
                                           ie1 = middleStore.symbolicEnd();
           it1 != ie1; ++it1) {
        symbolicToInterpolant(
            it1->first, it1->second, substitution, replacements, coreOnly,
            storeIter->second,
            referenceStore->isInLeftSubtree(it1->second->getDepth()));
      }
    }
  }

  for (LowerStateStore::const_iterator
           it = symbolicallyAddressedHistoricalStore.begin(),
           ie = symbolicallyAddressedHistoricalStore.end();
       it != ie; ++it) {
    symbolicToInterpolant(
        it->first, it->second, substitution, replacements, coreOnly,
        _symbolicallyAddressedHistoricalStore,
        referenceStore->isInLeftSubtree(it->second->getDepth()));
  }
}

void TxStore::updateStoreWithLoadedValue(
    std::map<llvm::Value *, std::vector<ref<TxStateValue> > > &valuesMap,
    ref<TxStateAddress> loc, ref<TxStateValue> address,
    ref<TxStateValue> value) {
  updateStore(valuesMap, loc, address, value);
  value->addLoadAddress(address);
}

void TxStore::updateStore(
    std::map<llvm::Value *, std::vector<ref<TxStateValue> > > &valuesMap,
    ref<TxStateAddress> location, ref<TxStateValue> address,
    ref<TxStateValue> value) {
  if (location.isNull())
    return;

  // Here we also mark the entries used to build the value as used. Only used
  // entries will be in the interpolant
  markUsed(value->getAllowBoundEntryList());
  markUsed(value->getDisableBoundEntryList());

  TopStateStore::iterator middleStoreIter =
      internalStore.find(location->getContext());

  if (middleStoreIter != internalStore.end()) {
    MiddleStateStore &middleStore = middleStoreIter->second;
    if (middleStore.hasAllocationInfo(location->getAllocationInfo())) {
      if (value->getDepth() < depth) {
        value = value->copy(depth);
        valuesMap[value->getValue()].push_back(value);
      }
      ref<TxStoreEntry> entry =
          middleStore.updateStore(this, location, address, value, depth);
      if (!entry.isNull()) {
        // We want to renew the table entry list, so we first remove the old
        // ones
        value->resetStoreEntryList();

        // We associate this value with the store entry, signifying that the
        // entry is important whenever the value is used. This is used for
        // computing the interpolant.
        value->addStoreEntry(entry);
      }
      return;
    }

    // Here we save the old store
    concretelyAddressedHistoricalStore.insert(middleStore.concreteBegin(),
                                              middleStore.concreteEnd());
    symbolicallyAddressedHistoricalStore.insert(middleStore.symbolicBegin(),
                                                middleStore.symbolicEnd());
  }

  MiddleStateStore newMiddleStateStore(location->getAllocationInfo());
  internalStore[location->getContext()] = newMiddleStateStore;
  MiddleStateStore &middleStateStore = internalStore[location->getContext()];
  if (value->getDepth() < depth) {
    value = value->copy(depth);
    valuesMap[value->getValue()].push_back(value);
  }
  ref<TxStoreEntry> entry =
      middleStateStore.updateStore(this, location, address, value, depth);
  if (!entry.isNull()) {
    // We associate this value with the store entry, signifying that the entry
    // is important whenever the value is used. This is used for computing the
    // interpolant.
    value->addStoreEntry(entry);
  }
}

void TxStore::markUsed(const std::set<ref<TxStoreEntry> > &entryList) {
  for (std::set<ref<TxStoreEntry> >::const_iterator it = entryList.begin(),
                                                    ie = entryList.end();
       it != ie; ++it) {
    uint64_t entryDepth = (*it)->getDepth();

    // Note that it is possible that entryDepth > depth, due to the association
    // of values with newly-created entries in TxStore::updateStore().
    if (entryDepth >= depth)
      continue;

    // We now register the used entry as used after it was instantiated in
    // previous depth levels
    TxStore *prev = 0, *current = parent;
    while (current && entryDepth <= current->depth) {
      const TxStore *constPrev;
      if (!prev) {
        constPrev = this;
      } else {
        constPrev = prev;
      }
      if (current->left == constPrev) {
        std::set<ref<TxStoreEntry> >::iterator usedEntryIter =
            current->usedByLeftPath.find(*it);
        if (usedEntryIter == current->usedByLeftPath.end()) {
          current->usedByLeftPath.insert(*it);
        } else {
          break;
        }
      } else if (current->right == constPrev) {
        std::set<ref<TxStoreEntry> >::iterator usedEntryIter =
            current->usedByRightPath.find(*it);
        if (usedEntryIter == current->usedByRightPath.end()) {
          current->usedByRightPath.insert(*it);
        } else {
          break;
        }
      } else {
        assert(!"child is neither left not right");
      }
      prev = current;
      current = current->parent;
    }
  }
}

void TxStore::recursivelyMarkFlow(ref<TxStoreEntry> entry, bool leftMarking,
                                  const std::string &reason) const {
  if (entry.isNull())
    return;

  if (entry->isCore(leftMarking)) {
    if (!entry->canInterpolateBound(leftMarking))
      return;
  }

  entry->setAsCore(leftMarking, reason);
  entry->disableBoundInterpolation(leftMarking);

  std::map<ref<TxStoreEntry>, bool> &allowBoundEntryList(
      entry->getAllowBoundEntryList());
  for (std::map<ref<TxStoreEntry>, bool>::iterator
           it = allowBoundEntryList.begin(),
           ie = allowBoundEntryList.end();
       it != ie; ++it) {
    recursivelyMarkFlow(it->first, it->second, reason);
  }

  std::map<ref<TxStoreEntry>, bool> &disableBoundEntryList(
      entry->getDisableBoundEntryList());
  for (std::map<ref<TxStoreEntry>, bool>::iterator
           it = disableBoundEntryList.begin(),
           ie = disableBoundEntryList.end();
       it != ie; ++it) {
    recursivelyMarkFlow(it->first, it->second, reason);
  }
}

void TxStore::markFlow(ref<TxStateValue> target,
                       const std::string &reason) const {
  if (target.isNull())
    return;

  const std::set<ref<TxStoreEntry> > &allowBoundEntryList(
      target->getAllowBoundEntryList());
  for (std::set<ref<TxStoreEntry> >::const_iterator
           it = allowBoundEntryList.begin(),
           ie = allowBoundEntryList.end();
       it != ie; ++it) {
    recursivelyMarkFlow(*it, isInLeftSubtree((*it)->getDepth()), reason);
  }

  const std::set<ref<TxStoreEntry> > &disableBoundEntryList(
      target->getDisableBoundEntryList());
  for (std::set<ref<TxStoreEntry> >::const_iterator
           it = disableBoundEntryList.begin(),
           ie = disableBoundEntryList.end();
       it != ie; ++it) {
    recursivelyMarkFlow(*it, isInLeftSubtree((*it)->getDepth()), reason);
  }
}

bool TxStore::recursivelyMarkPointerFlow(ref<TxStoreEntry> entry,
                                         bool leftMarking,
                                         ref<TxStateValue> checkedAddress,
                                         std::set<uint64_t> &bounds,
                                         const std::string &reason,
                                         uint64_t startingDepth) const {
  bool memoryError = false;
  bool boundUpdated = false;

  if (entry.isNull())
    return memoryError;

  if (entry->getDepth() == startingDepth) {
    memoryError = adjustOffsetBound(entry, true, checkedAddress, bounds, reason,
                                    boundUpdated)
                      ? true
                      : memoryError;
    memoryError = adjustOffsetBound(entry, false, checkedAddress, bounds,
                                    reason, boundUpdated)
                      ? true
                      : memoryError;
  } else {
    memoryError = adjustOffsetBound(entry, leftMarking, checkedAddress, bounds,
                                    reason, boundUpdated)
                      ? true
                      : memoryError;
  }

  if (memoryError) {
    std::map<ref<TxStoreEntry>, bool> &allowBoundEntryList(
        entry->getAllowBoundEntryList());
    for (std::map<ref<TxStoreEntry>, bool>::iterator
             it = allowBoundEntryList.begin(),
             ie = allowBoundEntryList.end();
         it != ie; ++it) {
      recursivelyMarkFlow(it->first, it->second, reason);
    }
  } else {
    if (boundUpdated) {
      std::map<ref<TxStoreEntry>, bool> &allowBoundEntryList(
          entry->getAllowBoundEntryList());
      for (std::map<ref<TxStoreEntry>, bool>::iterator
               it = allowBoundEntryList.begin(),
               ie = allowBoundEntryList.end();
           it != ie; ++it) {
        if (!it->first->isPointer()) {
          recursivelyMarkFlow(it->first, it->second, reason);
        } else {
          memoryError =
              recursivelyMarkPointerFlow(it->first, it->second, checkedAddress,
                                         bounds, reason, startingDepth)
                  ? true
                  : memoryError;
        }
      }
    }
  }

  std::map<ref<TxStoreEntry>, bool> &disableBoundEntryList(
      entry->getDisableBoundEntryList());
  for (std::map<ref<TxStoreEntry>, bool>::iterator
           it = disableBoundEntryList.begin(),
           ie = disableBoundEntryList.end();
       it != ie; ++it) {
    recursivelyMarkFlow(it->first, it->second, reason);
  }

  return memoryError;
}

bool TxStore::markPointerFlow(ref<TxStateValue> target,
                              ref<TxStateValue> checkedAddress,
                              std::set<uint64_t> &bounds,
                              const std::string &reason) const {
  bool memoryError = false;

  if (target.isNull())
    return memoryError;

  const std::set<ref<TxStoreEntry> > &allowBoundEntryList(
      target->getAllowBoundEntryList());
  for (std::set<ref<TxStoreEntry> >::const_iterator
           it = allowBoundEntryList.begin(),
           ie = allowBoundEntryList.end();
       it != ie; ++it) {
    if (!(*it)->isPointer()) {
      recursivelyMarkFlow(*it, isInLeftSubtree((*it)->getDepth()), reason);
    } else {
      memoryError =
          recursivelyMarkPointerFlow(*it, isInLeftSubtree((*it)->getDepth()),
                                     checkedAddress, bounds, reason, depth)
              ? true
              : memoryError;
    }
  }

  const std::set<ref<TxStoreEntry> > &disableBoundEntryList(
      target->getDisableBoundEntryList());
  for (std::set<ref<TxStoreEntry> >::const_iterator
           it = disableBoundEntryList.begin(),
           ie = disableBoundEntryList.end();
       it != ie; ++it) {
    recursivelyMarkFlow(*it, isInLeftSubtree((*it)->getDepth()), reason);
  }

  return memoryError;
}

/// \brief Print the content of the object to the LLVM error stream
void TxStore::print(llvm::raw_ostream &stream) const { this->print(stream, 0); }

void TxStore::print(llvm::raw_ostream &stream,
                    const unsigned paddingAmount) const {
  std::string tabs = makeTabs(paddingAmount);
  std::string tabsNext = appendTab(tabs);
  std::string tabsNextNext = appendTab(tabsNext);

  stream << tabs << "store = [";
  if (!internalStore.empty()) {
    stream << "\n";
    for (TopStateStore::const_iterator topIs = internalStore.begin(),
                                       topIe = internalStore.end(),
                                       topIt = topIs;
         topIt != topIe; ++topIt) {
      if (topIt != topIs) {
        stream << "\n";
      }
      topIt->first->print(stream, tabsNext);
      stream << ":\n";
      topIt->second.print(stream, tabsNextNext);
    }
    stream << tabs;
  }
  stream << "]";

  stream << "\n" << tabs << "concretely-addressed historical store = [";
  if (!concretelyAddressedHistoricalStore.empty()) {
    stream << "\n";
    for (TxStore::LowerStateStore::const_iterator
             is1 = concretelyAddressedHistoricalStore.begin(),
             ie1 = concretelyAddressedHistoricalStore.end(), it1 = is1;
         it1 != ie1; ++it1) {
      if (it1 != is1)
        stream << tabsNext << "------------------------------------------\n";
      it1->second->print(stream, tabsNext);
      stream << "\n";
    }
    stream << tabs;
  }
  stream << "]";

  stream << "\n" << tabs << "symbolically-addressed historical store = [";
  if (!symbolicallyAddressedHistoricalStore.empty()) {
    stream << "\n";
    for (TxStore::LowerStateStore::const_iterator
             is1 = symbolicallyAddressedHistoricalStore.begin(),
             ie1 = symbolicallyAddressedHistoricalStore.end(), it1 = is1;
         it1 != ie1; ++it1) {
      if (it1 != is1)
        stream << tabsNext << "------------------------------------------\n";
      it1->second->print(stream, tabsNext);
      stream << "\n";
    }
    stream << tabs;
  }
  stream << "]";
}
}
