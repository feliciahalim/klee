//===--- StoreFrame.h -------------------------------------------*- C++ -*-===//
//
//               The Tracer-X KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_STOREFRAME_H
#define KLEE_STOREFRAME_H

#include "klee/Internal/Module/VersionedValue.h"

#include <map>

namespace klee {

/// \brief Class defining local and global frames of store
class StoreFrame {
  /// \brief The mapping of concrete locations to stored value
  std::map<ref<MemoryLocation>,
           std::pair<ref<VersionedValue>, ref<VersionedValue> > >
  concretelyAddressedStore;

  /// \brief The mapping of symbolic locations to stored value
  std::map<ref<MemoryLocation>,
           std::pair<ref<VersionedValue>, ref<VersionedValue> > >
  symbolicallyAddressedStore;

public:
  StoreFrame() {}

  ~StoreFrame() {
    // Delete the locally-constructed relations
    concretelyAddressedStore.clear();
    symbolicallyAddressedStore.clear();
  }

  static StoreFrame &create() {
    StoreFrame *ret = new StoreFrame();
    return (*ret);
  }

  std::map<ref<MemoryLocation>,
           std::pair<ref<VersionedValue>, ref<VersionedValue> > > &
  getConcreteStore() {
    return concretelyAddressedStore;
  }

  std::map<ref<MemoryLocation>,
           std::pair<ref<VersionedValue>, ref<VersionedValue> > > &
  getSymbolicStore() {
    return symbolicallyAddressedStore;
  }

  void updateStore(ref<MemoryLocation> loc, ref<VersionedValue> address,
                   ref<VersionedValue> value) {
    if (loc->hasConstantAddress()) {
      concretelyAddressedStore[loc] =
          std::pair<ref<VersionedValue>, ref<VersionedValue> >(address, value);
    } else {
      symbolicallyAddressedStore[loc] =
          std::pair<ref<VersionedValue>, ref<VersionedValue> >(address, value);
    }
  }

  std::pair<ref<VersionedValue>, ref<VersionedValue> >
  read(ref<MemoryLocation> address) {
    std::pair<ref<VersionedValue>, ref<VersionedValue> > ret;
    std::map<ref<MemoryLocation>,
             std::pair<ref<VersionedValue>,
                       ref<VersionedValue> > >::const_iterator it;
    if (address->hasConstantAddress()) {
      it = concretelyAddressedStore.find(address);
      if (it != concretelyAddressedStore.end())
        ret = it->second;
    } else {
      it = symbolicallyAddressedStore.find(address);
      // FIXME: Here we assume that the expressions have to exactly be the
      // same expression object. More properly, this should instead add an
      // ite constraint onto the path condition.
      if (it != symbolicallyAddressedStore.end())
        ret = it->second;
    }
    return ret;
  }

  void print(llvm::raw_ostream &stream) const { print(stream, ""); }

  void print(llvm::raw_ostream &stream, const std::string &prefix) const;

  void dump() const {
    print(llvm::errs());
    llvm::errs() << "\n";
  }
};
}

#endif // KLEE_STOREFRAME_H
