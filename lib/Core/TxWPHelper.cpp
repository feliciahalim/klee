//===-- TxWPHelper.cpp - Interpolation tree -------------------------*- C++
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
/// This file contains the implementations of helper function for generating
/// weakest
/// precondition.
///
//===----------------------------------------------------------------------===//

#include "TxWPHelper.h"
#include "TxTree.h"

namespace klee {

bool TxWPHelper::isTargetDependent(llvm::Value *inst, ref<Expr> expr) {
  switch (expr->getKind()) {
  case Expr::InvalidKind:
  case Expr::Constant: { return false; }

  case Expr::WPVar: {
    ref<WPVarExpr> wp1 = dyn_cast<WPVarExpr>(expr);
    // if inst is an alloca & empty name
    // find its corresponding function argument
    llvm::Value *arg = 0;
    if (isa<llvm::AllocaInst>(inst)) {
      llvm::AllocaInst *alc = dyn_cast<llvm::AllocaInst>(inst);
      if (alc->getName().empty()) {
        llvm::Instruction *tmp = alc->getNextNode();
        while (true) {
          if (isa<llvm::StoreInst>(tmp) && tmp->getOperand(1) == alc) {
            arg = tmp->getOperand(0);
            break;
          } else {
            tmp = tmp->getNextNode();
            if (tmp->isTerminator()) {
              break;
            }
          }
        }
      }
    }
    if (arg && arg == wp1->address) {
      return true;
    } else {
      if (wp1->address == inst) {
        return true;
      } else {
        return false;
      }
    }
  }

  case Expr::NotOptimized:
  case Expr::Not:
  case Expr::Extract:
  case Expr::ZExt:
  case Expr::SExt: {
    ref<Expr> kids[1];
    kids[0] = expr->getKid(0);
    return isTargetDependent(inst, kids[0]);
  }

  case Expr::Eq:
  case Expr::Ne:
  case Expr::Ult:
  case Expr::Ule:
  case Expr::Ugt:
  case Expr::Uge:
  case Expr::Slt:
  case Expr::Sle:
  case Expr::Sgt:
  case Expr::Sge:
  case Expr::LastKind:
  case Expr::Add:
  case Expr::Sub:
  case Expr::Mul:
  case Expr::UDiv:
  case Expr::SDiv:
  case Expr::URem:
  case Expr::SRem:
  case Expr::And:
  case Expr::Or:
  case Expr::Xor:
  case Expr::Shl:
  case Expr::LShr:
  case Expr::AShr: {
    ref<Expr> kids[2];
    kids[0] = expr->getKid(0);
    kids[1] = expr->getKid(1);
    return (isTargetDependent(inst, kids[0]) ||
            isTargetDependent(inst, kids[1]));
  }

  case Expr::Select: {
    ref<Expr> kids[3];
    kids[0] = expr->getKid(0);
    kids[1] = expr->getKid(1);
    kids[2] = expr->getKid(2);
    return (isTargetDependent(inst, kids[0]) ||
            isTargetDependent(inst, kids[1]) ||
            isTargetDependent(inst, kids[2]));
  }
  case Expr::Upd: {
    ref<Expr> kids[3];
    kids[0] = expr->getKid(0);
    kids[1] = expr->getKid(1);
    kids[2] = expr->getKid(2);
    return (isTargetDependent(inst, kids[0]) ||
            isTargetDependent(inst, kids[1]) ||
            isTargetDependent(inst, kids[2]));
  }
  case Expr::Sel: {
    ref<Expr> kids[2];
    kids[0] = expr->getKid(0);
    kids[1] = expr->getKid(1);
    return (isTargetDependent(inst, kids[0]) ||
            isTargetDependent(inst, kids[1]));
  }
  default: {
    // Sanity check
    expr->dump();
    klee_error("Control should not reach here in "
               "TxWPHelper::isTargetDependent!");
  }
  }
  return false;
}

ref<Expr> TxWPHelper::substituteExpr(ref<Expr> base, const ref<Expr> lhs,
                                     const ref<Expr> rhs) {

  if (rhs.isNull()) {
    return rhs;
  } else if (base.compare(lhs) == 0) { // base case
    return rhs;
  } else {
    switch (base->getKind()) {
    case Expr::InvalidKind:
    case Expr::Constant: { return base; }

    case Expr::WPVar: {
      ref<WPVarExpr> wp1 = dyn_cast<WPVarExpr>(base);
      ref<WPVarExpr> wp2 = dyn_cast<WPVarExpr>(lhs);
      if (wp1->address == wp2->address) {
        return rhs;
      } else
        return base;
    }

    case Expr::NotOptimized:
    case Expr::Not:
    case Expr::Extract:
    case Expr::ZExt:
    case Expr::SExt: {
      ref<Expr> kids[1];
      kids[0] = substituteExpr(base->getKid(0), lhs, rhs);
      if (kids[0].isNull())
        return kids[0];
      else
        return base->rebuild(kids);
    }

    case Expr::Sel:
    case Expr::Concat:
    case Expr::Eq:
    case Expr::Ne:
    case Expr::Ult:
    case Expr::Ule:
    case Expr::Ugt:
    case Expr::Uge:
    case Expr::Slt:
    case Expr::Sle:
    case Expr::Sgt:
    case Expr::Sge:
    case Expr::LastKind:
    case Expr::Add:
    case Expr::Sub:
    case Expr::Mul:
    case Expr::UDiv:
    case Expr::SDiv:
    case Expr::URem:
    case Expr::SRem:
    case Expr::Shl:
    case Expr::LShr:
    case Expr::AShr: {
      ref<Expr> kids[2];
      kids[0] = substituteExpr(base->getKid(0), lhs, rhs);
      kids[1] = substituteExpr(base->getKid(1), lhs, rhs);

      if (kids[0].isNull())
        return kids[0];
      else if (kids[1].isNull())
        return kids[1];
      else
        return base->rebuild(kids);
    }

    case Expr::And:
    case Expr::Or:
    case Expr::Xor: {
      ref<Expr> kids[2];
      kids[0] = substituteExpr(base->getKid(0), lhs, rhs);
      kids[1] = substituteExpr(base->getKid(1), lhs, rhs);
      if (kids[0].isNull())
        return kids[1];
      else if (kids[1].isNull())
        return kids[0];
      else
        return base->rebuild(kids);
    }

    case Expr::Upd:
    case Expr::Select: {
      ref<Expr> kids[3];
      kids[0] = substituteExpr(base->getKid(0), lhs, rhs);
      kids[1] = substituteExpr(base->getKid(1), lhs, rhs);
      kids[2] = substituteExpr(base->getKid(2), lhs, rhs);
      if (kids[0].isNull())
        return kids[0];
      else if (kids[1].isNull())
        return kids[1];
      else if (kids[2].isNull())
        return kids[2];
      else
        return base->rebuild(kids);
    }

    default: {
      base->dump();
      lhs->dump();
      rhs->dump();
      klee_error("TxWPHelper::substituteExpr: Expression not supported yet!");
    }
    }
  }

  return base;
}

llvm::Instruction *TxWPHelper::getNearestCallInst(const llvm::Value *ins,
                                                  TxTreeNode *txNode) {
  TxTreeNode *tmp = txNode;
  llvm::Instruction *lastCall = NULL;
  while (tmp != NULL) {
    bool found = false;
    for (std::vector<std::pair<KInstruction *, int> >::iterator
             it = tmp->reverseInstructionList.begin(),
             ie = tmp->reverseInstructionList.end();
         it != ie; ++it) {
      if (isa<llvm::CallInst>(it->first->inst)) {
        lastCall = (it->first->inst);
      }
      if (ins == it->first->inst) {
        found = true;
        break;
      }
    }

    if (found) {
      break;
    } else {
      tmp = tmp->getParent();
    }
  }
  return lastCall;
}

} /* namespace klee */
