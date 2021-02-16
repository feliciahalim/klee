//===-- TxWPHelper.h - Tracer-X symbolic execution tree -------------*- C++
//-*-===//
//
//               The Tracer-X KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// This file contains declarations of the classes that support for generating
/// weakest precondition interpolation.
///
//===----------------------------------------------------------------------===//

#ifndef LIB_CORE_TXWPHELPER_H_
#define LIB_CORE_TXWPHELPER_H_

#include "TxWP.h"
#include "klee/ExecutionState.h"
#include <klee/Expr.h>
#include <klee/ExprBuilder.h>
#include <klee/Internal/Support/ErrorHandling.h>
#include <klee/util/ArrayCache.h>
#include <vector>
#include "TxSpeculation.h"

namespace klee {

class TxWPArrayStore;

class TxWPHelper {

public:
  static bool isTargetDependent(llvm::Value *inst, ref<Expr> expr);

  static ref<Expr> substituteExpr(ref<Expr> base, const ref<Expr> lhs,
                                  const ref<Expr> rhs);

  static llvm::Instruction *getNearestCallInst(const llvm::Value *ins,
                                               TxTreeNode *txNode);

  // get function argument
    static  llvm::Value* getnthArgument(const llvm::Value *ins, int nth) {
    	const llvm::Function *f =
          dyn_cast<llvm::Instruction>(ins)->getParent()->getParent();
      if(f->getArgumentList().empty()) {
    	  return NULL;
      }
      int i=0;
      const llvm::Argument* a=f->getArgumentList().begin();
      while(i<nth){
    	  a=a->getNextNode();
    	  ++i;
      }
      return const_cast<llvm::Argument*>(a);
    }

  // return the order of parameter of the function
  // if ins is not allocation for parameter then return -1
  static int isParamAlloca(const llvm::Value *ins) {
    const llvm::Function *f =
        dyn_cast<llvm::Instruction>(ins)->getParent()->getParent();
    int ret = -1;
    std::vector<const llvm::Instruction *> paramAllocas = getParamsAllocas(f);
    for (unsigned int i = 0; i < paramAllocas.size(); ++i) {
      if (paramAllocas[i] == ins) {
        ret = i;
        break;
      }
    }
    return ret;
  }

  // get the first of store instruction of the function
  // if
  static bool isRetAlloca(const llvm::Value *ins) {
    // ins->dump();
    const llvm::Function *f =
        dyn_cast<llvm::Instruction>(ins)->getParent()->getParent();
    // if void function then return false;
    if (f->getReturnType()->getTypeID() == llvm::Type::VoidTyID) {
      return false;
    }

    std::vector<const llvm::Instruction *> fAllocas = getFirstAllocas(f);
    if (fAllocas.empty()) {
      return false;
    }

    if (ins != fAllocas[0]) {
      return false;
    }

    // if ins is in parameter alloca then return false
    std::vector<const llvm::Instruction *> paramAllocas = getParamsAllocas(f);
    for (std::vector<const llvm::Instruction *>::iterator
             it = paramAllocas.begin(),
             ie = paramAllocas.end();
         it != ie; ++it) {
      if (ins == (*it)) {
        return false;
      }
    }

    return true;
  }

  // get all top store instructions of the function
  static std::vector<const llvm::Instruction *>
  getFirstStores(const llvm::Function *f) {
    const llvm::Instruction *tmp = &f->front().front();
    bool hasStore = false;
    while (!tmp->isTerminator()) {
      if (isa<llvm::StoreInst>(tmp)) {
        hasStore = true;
        break;
      } else {
        tmp = tmp->getNextNode();
      }
    }

    std::vector<const llvm::Instruction *> fstores;
    if (hasStore) {
      while (!tmp->isTerminator()) {
        if (isa<llvm::StoreInst>(tmp)) {
          fstores.push_back(tmp);
          tmp = tmp->getNextNode();
        } else {
          break;
        }
      }
    }
    return fstores;
  }

  // get all top alloca instructions of the function
  static std::vector<const llvm::Instruction *>
  getFirstAllocas(const llvm::Function *f) {
    const llvm::Instruction *tmp = &f->front().front();
    std::vector<const llvm::Instruction *> fallocas;
    while (!tmp->isTerminator()) {
      if (isa<llvm::AllocaInst>(tmp)) {
        fallocas.push_back(tmp);
        tmp = tmp->getNextNode();
      } else {
        break;
      }
    }
    return fallocas;
  }

  // get all top store instructions of the function
  // if each store instruction is to save function argument the location is the
  // alloca
  static std::vector<const llvm::Instruction *>
  getParamsAllocas(const llvm::Function *f) {
    std::vector<const llvm::Instruction *> fstores = getFirstStores(f);
    std::vector<const llvm::Instruction *> pAllocas;
    for (std::vector<const llvm::Instruction *>::iterator it = fstores.begin(),
                                                          ie = fstores.end();
         it != ie; ++it) {
      for (llvm::Function::const_arg_iterator it1 = f->arg_begin(),
                                              ie1 = f->arg_end();
           it1 != ie1; ++it1) {
        if (it1 == (*it)->getOperand(0)) {
          pAllocas.push_back(dyn_cast<llvm::Instruction>((*it)->getOperand(1)));
        }
      }
    }
    return pAllocas;
  }

  static std::string getNoNameInst(const llvm::Value *i) {
    if (!i->getName().empty())
      return i->getName().str();
    std::string Str;
    llvm::raw_string_ostream OS(Str);
    i->print(OS);
    unsigned pos = OS.str().find("=");
    return TxSpeculationHelper::trim(OS.str().substr(0, pos));
  }

  static bool isSkipPushUp(std::string fname) {
    if ((fname.substr(0, 5) == "klee_") || (fname.substr(0, 3) == "tx_") ||
        (fname == "printf") || (fname.substr(0, 6) == "check_") ||
        (fname.substr(0, 6) == "memcpy")) {
      return true;
    }
    return false;
  }
};

} /* namespace klee */

#endif /* LIB_CORE_TXWPHELPER_H_ */
