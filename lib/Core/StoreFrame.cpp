//===-- StoreFrame.cpp ------------------------------------------*- C++ -*-===//
//
//               The Tracer-X KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "StoreFrame.h"
#include "TxPrintUtil.h"

#include "klee/CommandLine.h"

using namespace klee;

namespace klee {

StoreFrame *StoreFrame::findFrame(const ref<MemoryLocation> loc) {
  std::vector<llvm::Instruction *> callHistory =
      loc->getContext()->getCallHistory();
  const uint64_t historyHeight = callHistory.size();

  if (height < historyHeight)
    return 0;

  StoreFrame *current = this;
  for (uint64_t i = height; i > historyHeight; --i) {
    current = current->parent;
  }

  // Strictly speaking, we need to check that all elements match, but here we
  // just do a quick check that the top callsites match.
  if (current->callsite == 0 && callHistory.empty())
    return current;

  if (current->callsite == callHistory.back())
    return current;

  return 0;
}

std::pair<bool, std::map<ref<MemoryLocation>,
                         std::pair<ref<VersionedValue>,
                                   ref<VersionedValue> > >::const_iterator>
StoreFrame::findInConcreteStore(ref<MemoryLocation> loc) const {
  std::pair<bool, std::map<ref<MemoryLocation>,
                           std::pair<ref<VersionedValue>,
                                     ref<VersionedValue> > >::const_iterator>
  ret;
  const std::map<ref<MemoryLocation>,
                 std::pair<ref<VersionedValue>, ref<VersionedValue> > > &store =
      (source ? source->concretelyAddressedStore : concretelyAddressedStore);
  ret.second = store.find(loc);
  ret.first = (ret.second != store.end());
  return ret;
}

std::pair<bool, std::map<ref<MemoryLocation>,
                         std::pair<ref<VersionedValue>,
                                   ref<VersionedValue> > >::const_iterator>
StoreFrame::findInSymbolicStore(ref<MemoryLocation> loc) const {
  std::pair<bool, std::map<ref<MemoryLocation>,
                           std::pair<ref<VersionedValue>,
                                     ref<VersionedValue> > >::const_iterator>
  ret;
  const std::map<ref<MemoryLocation>,
                 std::pair<ref<VersionedValue>, ref<VersionedValue> > > &store =
      (source ? source->symbolicallyAddressedStore
              : symbolicallyAddressedStore);
  ret.second = store.find(loc);
  ret.first = (ret.second != store.end());
  return ret;
}

void StoreFrame::updateStore(ref<MemoryLocation> loc,
                             ref<VersionedValue> address,
                             ref<VersionedValue> value) {

  StoreFrame *frame = this;

  if (!loc->isGlobal())
    frame = findFrame(loc);

  assert(frame && "frame not found");

  // We copy the store to update on demand, only when this function is invoked
  if (frame->source) {
    frame->concretelyAddressedStore = frame->source->concretelyAddressedStore;
    frame->symbolicallyAddressedStore =
        frame->source->symbolicallyAddressedStore;
    frame->source = 0;
  }

  if (loc->hasConstantAddress()) {
    (frame->concretelyAddressedStore)[loc] =
        std::pair<ref<VersionedValue>, ref<VersionedValue> >(address, value);
  } else {
    (frame->symbolicallyAddressedStore)[loc] =
        std::pair<ref<VersionedValue>, ref<VersionedValue> >(address, value);
  }
}

std::pair<ref<VersionedValue>, ref<VersionedValue> >
StoreFrame::read(ref<MemoryLocation> address) {
  std::map<
      ref<MemoryLocation>,
      std::pair<ref<VersionedValue>, ref<VersionedValue> > >::const_iterator it;

  StoreFrame *frame = this;

  if (!address->isGlobal())
    frame = findFrame(address);

  assert(frame && "frame not found");

  if (address->hasConstantAddress()) {
    const std::map<ref<MemoryLocation>,
                   std::pair<ref<VersionedValue>, ref<VersionedValue> > > &
    concreteStore = (frame->source ? frame->source->concretelyAddressedStore
                                   : frame->concretelyAddressedStore);
    it = concreteStore.find(address);
    if (it != concreteStore.end())
      return it->second;
  } else {
    const std::map<ref<MemoryLocation>,
                   std::pair<ref<VersionedValue>, ref<VersionedValue> > > &
    symbolicStore = (frame->source ? frame->source->symbolicallyAddressedStore
                                   : frame->symbolicallyAddressedStore);
    it = symbolicStore.find(address);
    // FIXME: Here we assume that the expressions have to exactly be the
    // same expression object. More properly, this should instead add an
    // ite constraint onto the path condition.
    if (it != symbolicStore.end())
      return it->second;
  }

  std::pair<ref<VersionedValue>, ref<VersionedValue> > dummyReturnValue;
  return dummyReturnValue;
}

void StoreFrame::getConcreteStore(
    const std::vector<llvm::Instruction *> &callHistory,
    std::set<const Array *> &replacements, bool coreOnly,
    TxConcreteStore &concreteStore) const {
  const std::map<ref<MemoryLocation>,
                 std::pair<ref<VersionedValue>, ref<VersionedValue> > > &store =
      (source ? source->concretelyAddressedStore : concretelyAddressedStore);

  for (std::map<ref<MemoryLocation>,
                std::pair<ref<VersionedValue>,
                          ref<VersionedValue> > >::const_iterator
           it = store.begin(),
           ie = store.end();
       it != ie; ++it) {
    if (!it->first->contextIsPrefixOf(callHistory))
      continue;

    if (it->second.second.isNull())
      continue;

    if (!coreOnly) {
      const llvm::Value *base = it->first->getContext()->getValue();
      concreteStore[base][StoredAddress::create(it->first)] =
          StoredValue::create(it->second.second);
    } else if (it->second.second->isCore()) {
      // An address is in the core if it stores a value that is in the core
      const llvm::Value *base = it->first->getContext()->getValue();
#ifdef ENABLE_Z3
      if (!NoExistential) {
        concreteStore[base][StoredAddress::create(it->first)] =
            StoredValue::create(it->second.second, replacements);
      } else
#endif
        concreteStore[base][StoredAddress::create(it->first)] =
            StoredValue::create(it->second.second);
    }
  }
}

void StoreFrame::getSymbolicStore(
    const std::vector<llvm::Instruction *> &callHistory,
    std::set<const Array *> &replacements, bool coreOnly,
    TxSymbolicStore &symbolicStore) const {
  const std::map<ref<MemoryLocation>,
                 std::pair<ref<VersionedValue>, ref<VersionedValue> > > &store =
      (source ? source->symbolicallyAddressedStore
              : symbolicallyAddressedStore);

  for (std::map<ref<MemoryLocation>,
                std::pair<ref<VersionedValue>,
                          ref<VersionedValue> > >::const_iterator
           it = store.begin(),
           ie = store.end();
       it != ie; ++it) {
    if (!it->first->contextIsPrefixOf(callHistory))
      continue;

    if (it->second.second.isNull())
      continue;

    if (!coreOnly) {
      llvm::Value *base = it->first->getContext()->getValue();
      symbolicStore[base].push_back(
          TxAddressValuePair(StoredAddress::create(it->first),
                             StoredValue::create(it->second.second)));
    } else if (it->second.second->isCore()) {
      // An address is in the core if it stores a value that is in the core
      llvm::Value *base = it->first->getContext()->getValue();
#ifdef ENABLE_Z3
      if (!NoExistential) {
        symbolicStore[base].push_back(TxAddressValuePair(
            StoredAddress::create(
                MemoryLocation::create(it->first, replacements)),
            StoredValue::create(it->second.second, replacements)));
      } else
#endif
        symbolicStore[base].push_back(
            TxAddressValuePair(StoredAddress::create(it->first),
                               StoredValue::create(it->second.second)));
    }
  }
}

void StoreFrame::print(llvm::raw_ostream &stream,
                       const std::string &prefix) const {
  std::string tabsNext = appendTab(prefix);
  std::string tabsNextNext = appendTab(tabsNext);

  const std::map<ref<MemoryLocation>,
                 std::pair<ref<VersionedValue>, ref<VersionedValue> > > &
  concreteStore =
      (source ? source->concretelyAddressedStore : concretelyAddressedStore);

  const std::map<ref<MemoryLocation>,
                 std::pair<ref<VersionedValue>, ref<VersionedValue> > > &
  symbolicStore = (source ? source->symbolicallyAddressedStore
                          : symbolicallyAddressedStore);

  if (concreteStore.empty()) {
    stream << prefix << "concrete store = []\n";
  } else {
    stream << prefix << "concrete store = [\n";
    for (std::map<ref<MemoryLocation>,
                  std::pair<ref<VersionedValue>,
                            ref<VersionedValue> > >::const_iterator
             is = concreteStore.begin(),
             ie = concreteStore.end(), it = is;
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
    stream << prefix << "]\n";
  }

  if (symbolicStore.empty()) {
    stream << prefix << "symbolic store = []\n";
  } else {
    stream << prefix << "symbolic store = [\n";
    for (std::map<ref<MemoryLocation>,
                  std::pair<ref<VersionedValue>,
                            ref<VersionedValue> > >::const_iterator
             is = symbolicStore.begin(),
             ie = symbolicStore.end(), it = is;
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
}
}
