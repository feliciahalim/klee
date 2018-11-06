//===-- TxWP.cpp - Interpolation tree -------------------------*- C++ -*-===//
//
//               The Tracer-X KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// This file contains the implementations of the classes for weakest
/// precondition.
///
//===----------------------------------------------------------------------===//

#include "TxWP.h"
#include "Context.h"
#include "TxTree.h"

#include <klee/Expr.h>
#include <klee/Internal/Support/ErrorHandling.h>

#include "TimingSolver.h"
#include "TxDependency.h"
#include "TxShadowArray.h"

#include <fstream>
#include <klee/CommandLine.h>
#include <klee/Solver.h>
#include <klee/SolverStats.h>
#include <klee/util/ExprPPrinter.h>
#include <klee/util/TxPrintUtil.h>
#include <vector>

using namespace klee;

typedef std::map<ref<TxVariable>, ref<TxInterpolantValue> >
    LowerInterpolantStore;
typedef std::map<ref<TxAllocationContext>, LowerInterpolantStore>
    TopInterpolantStore;

void TxWPArrayStore::insert(ref<TxAllocationContext> address,
                            const Array *array, ref<Expr> expr) {
  std::map<ref<TxAllocationContext>,
           std::pair<const Array *, ref<Expr> > >::iterator it =
      arrayStore.find(address);
  if (it == arrayStore.end()) {
    // value not found in map
    arrayStore.insert(std::make_pair(address, std::make_pair(array, expr)));
  } else {
    // case where value found in map so it's a memory location

    // sanity check
    if (it->second.first != array) {
      address->dump();
      expr->dump();
      klee_error("TxWPArrayStore::insert updating Expr value of wrong array.");
    }
    it->second = std::make_pair(array, expr);
  }
}

std::pair<unsigned int, unsigned int>
TxWPArrayStore::getSize(llvm::Value *value) {

  // Only catching the type of integer and pointers now
  // TODO: Add more types
  std::pair<unsigned int, unsigned int> size = std::make_pair(0, 0);
  if (value->getType()->isIntegerTy()) {
    size = this->getSize_aux(value->getType());
  } else if (value->getType()->isPointerTy()) {
    size = this->getSize_aux(value->getType());
    //  } else if (value->getType()->isPointerTy() &&
    //             value->getType()->getArrayElementType()->isPointerTy() &&
    //             value->getType()
    //                 ->getArrayElementType()
    //                 ->getArrayElementType()
    //                 ->isIntegerTy()) {
    //    size = value->getType()
    //               ->getArrayElementType()
    //               ->getArrayElementType()
    //               ->getIntegerBitWidth();
    //  } else if (value->getType()->isPointerTy() &&
    //             value->getType()->getArrayElementType()->isArrayTy() &&
    //             value->getType()
    //                 ->getArrayElementType()
    //                 ->getArrayElementType()
    //                 ->isIntegerTy()) {
    //    size = value->getType()
    //               ->getArrayElementType()
    //               ->getArrayElementType()
    //               ->getIntegerBitWidth();
  } else {
    value->dump();
    value->getType()->dump();
    klee_error(
        "TxWPArrayStore::createAndInsert getting size is not defined for this "
        "type yet");
  }

  return size;
}

std::pair<unsigned int, unsigned int>
TxWPArrayStore::getSize_aux(llvm::Type *type) {

  if (type->isIntegerTy()) {
    return std::make_pair(type->getIntegerBitWidth(),
                          type->getIntegerBitWidth());
  } else if (type->isPointerTy()) {
    return std::make_pair(
        this->getSize_aux(type->getArrayElementType()).first,
        this->getSize_aux(type->getArrayElementType()).second);
  } else if (type->isArrayTy()) {
    std::pair<unsigned int, unsigned int> size =
        this->getSize_aux(type->getArrayElementType());
    return std::make_pair(size.first,
                          size.second * type->getArrayNumElements());
  } else {
    type->dump();
    klee_error("TxWPArrayStore::getSize_aux: This type not yet implemented!");
    return std::make_pair(0, 0);
  }
}

ref<Expr> TxWPArrayStore::createAndInsert(ref<TxAllocationContext> address,
                                          std::string arrayName,
                                          llvm::Value *value,
                                          ref<Expr> offset) {

  std::map<ref<TxAllocationContext>,
           std::pair<const Array *, ref<Expr> > >::iterator it =
      arrayStore.find(address);

  // Getting the size of the value
  // First argument size of each cell
  // Second argument size of total array
  std::pair<unsigned int, unsigned int> size = getSize(value);

  array = ac.CreateArray(arrayName, size.second);

  ref<Expr> expr(0);
  unsigned NumBytes = size.first / 8;
  assert(size.first == NumBytes * 8 && "Invalid read size!");

  for (unsigned i = 0; i != NumBytes; ++i) {
    unsigned idx = Context::get().isLittleEndian() ? i : (NumBytes - i - 1);
    ref<Expr> updOffset = ConstantExpr::alloc(idx, array->getDomain());
    if (!offset.isNull())
      updOffset =
          AddExpr::create(offset, ConstantExpr::alloc(idx, array->getDomain()));

    ref<Expr> Byte = ReadExpr::create(UpdateList(array, 0), updOffset);
    expr = i ? ConcatExpr::create(Byte, expr) : Byte;
  }

  if (it == arrayStore.end()) {
    // value not found in map
    arrayStore.insert(std::make_pair(address, std::make_pair(array, expr)));

  } else {
    // Case where value found in map so it's a memory location

    // sanity check
    //    if (it->second.first != array) {
    //      address->dump();
    //      expr->dump();
    //      klee_error("TxWPArrayStore::createAndInsert updating Expr value of
    //      wrong "
    //                 "array.");
    //    }
    it->second = std::make_pair(array, expr);
  }
  return expr;
}

llvm::Value *TxWPArrayStore::getValuePointer(ref<Expr> expr) {
  ref<TxAllocationContext> address;
  for (std::map<ref<TxAllocationContext>,
                std::pair<const Array *, ref<Expr> > >::const_iterator
           it = arrayStore.begin(),
           ie = arrayStore.end();
       it != ie; ++it) {
    std::string name;
    if (llvm::isa<ReadExpr>(expr)) {
      name = llvm::dyn_cast<ReadExpr>(expr)->getName();
    } else if (llvm::isa<ConcatExpr>(expr)) {
      ref<ConcatExpr> concatVar = llvm::dyn_cast<ConcatExpr>(expr);
      name = llvm::dyn_cast<ReadExpr>(concatVar->getLeft())->getName();
    }
    if (it->first->getValue()->getName() == name) {
      address = it->first;
      return address->getValue();
    }
  }

  klee_warning("printing wpStore");
  for (std::map<ref<TxAllocationContext>,
                std::pair<const Array *, ref<Expr> > >::const_iterator
           it = arrayStore.begin(),
           ie = arrayStore.end();
       it != ie; ++it) {
    it->first->dump();
    it->second.second->dump();
  }
  klee_warning("End printing wpStore");
  expr->dump();
  klee_error("TxWPArrayStore::getValuePointer returning null");

  return NULL;
}

ref<TxAllocationContext> TxWPArrayStore::getAddress(ref<Expr> var) {
  ref<TxAllocationContext> address;
  for (std::map<ref<TxAllocationContext>,
                std::pair<const Array *, ref<Expr> > >::const_iterator
           it = arrayStore.begin(),
           ie = arrayStore.end();
       it != ie; ++it) {
    std::string name;
    if (llvm::isa<ReadExpr>(var)) {
      name = llvm::dyn_cast<ReadExpr>(var)->getName();
    } else if (llvm::isa<ConcatExpr>(var)) {
      ref<ConcatExpr> concatVar = llvm::dyn_cast<ConcatExpr>(var);
      name = llvm::dyn_cast<ReadExpr>(concatVar->getLeft())->getName();
    }
    if (it->first->getValue()->getName() == name) {
      address = it->first;
      return address;
    }
  }
  klee_warning("TxWPArrayStore::getAddress returning null for:");
  var->dump();
  return NULL;
}

ref<TxAllocationContext> TxWPArrayStore::getAddress(const Array *arr) {
  ref<TxAllocationContext> address;
  for (std::map<ref<TxAllocationContext>,
                std::pair<const Array *, ref<Expr> > >::const_iterator
           it = arrayStore.begin(),
           ie = arrayStore.end();
       it != ie; ++it) {
    std::string name = arr->getName();
    if (it->first->getValue()->getName() == name) {
      address = it->first;
      return address;
    }
  }
  klee_warning("TxWPArrayStore::getAddress returning null for:%s",
               arr->getName().c_str());
  return NULL;
}

ref<TxAllocationContext> TxWPArrayStore::getAddress(llvm::Value *i) {
  klee_error("TxWPArrayStore::getAddress");
  // TODO: to be implemented
  //  llvm::Instruction *inst;
  //  if (isa<llvm::Instruction>(i)) {
  //    inst = dyn_cast<llvm::Instruction>(i);
  //  } else if (isa<llvm::GlobalValue>(i)) {
  //    return "Global";
  //  } else if (isa<llvm::ConstantExpr>(i)) {
  //    // llvm::ConstantExpr* ce = dyn_cast<llvm::ConstantExpr>(i);
  //    // klee_error("TxWeTxWeakestPreConditiongetFunctionName");
  //    return "Constant";
  //  } else {
  //    i->dump();
  //    klee_error("TxWeakestPreCondition::getFunctionName LLVM Value is not an
  //    "
  //               "instruction");
  //  }
  //  llvm::BasicBlock *BB = inst->getParent();
  //  if (!BB) {
  //    inst->dump();
  //    klee_error("TxWeakestPreCondition::getFunctionName Basic Block is
  //    Null");
  //  }
  //  llvm::Function *func = BB->getParent();
  //  if (!func) {
  //    BB->dump();
  //    klee_error("TxWeakestPreCondition::getFunctionName Function is Null");
  //  }
  //  if (!func->hasName()) {
  //    func->dump();
  //    klee_error("TxWeakestPreCondition::getFunctionName Function has no
  //    name");
  //  }
  //  return func->getName();
}

ref<Expr> TxWPArrayStore::getExpr(ref<TxAllocationContext> address) {
  return arrayStore.find(address)->second.second;
}

const Array *TxWPArrayStore::getArray(ref<TxAllocationContext> address) {
  return arrayStore.find(address)->second.first;
}

/**/

TxWeakestPreCondition::TxWeakestPreCondition(TxTreeNode *_node,
                                             TxDependency *_dependency) {
  WPExpr = True();
  wpStore = new TxWPArrayStore();
  wpStore->array = wpStore->ac.CreateArray("const", 128);
  wpStore->constValues = ConstantExpr::create(0, 32);

  // Used to represent constants during the simplification of WPExpr to
  // canonical form
  node = _node;
  dependency = _dependency;
  if (dependency)
    debugSubsumptionLevel = dependency->debugSubsumptionLevel;
}

TxWeakestPreCondition::~TxWeakestPreCondition() {}

// std::vector<std::pair<KInstruction *, int> >
// TxWeakestPreCondition::markVariables(
//    std::vector<std::pair<KInstruction *, int> > reverseInstructionList) {
//
//  for (std::vector<std::pair<KInstruction *, int> >::const_reverse_iterator
//           it = reverseInstructionList.rbegin(),
//           ie = reverseInstructionList.rend();
//       it != ie; ++it) {
//
//    // Retrieve the instruction
//    KInstruction *i = (*it).first;
//
//    std::vector<std::pair<KInstruction *, int> >::iterator iter =
//        std::find(reverseInstructionList.begin(),
// reverseInstructionList.end(),
//                  std::pair<KInstruction *, int>(i, 0));
//
//    // Mark the instructions
//    if (markedVariables.find(i->inst) != markedVariables.end()) {
//      iter->second = 1;
//    } else if (dyn_cast<llvm::StoreInst>(i->inst) &&
//               markedVariables.find(i->inst->getOperand(1)) !=
//                   markedVariables.end()) {
//      iter->second = 1;
//    }
//
//    // Add the variables in the RHS of marked instructions to markedVariables
//    // set
//    if ((*it).second == 1) {
//      if (dyn_cast<llvm::BinaryOperator>(i->inst) ||
//          dyn_cast<llvm::LoadInst>(i->inst) ||
//          dyn_cast<llvm::UnaryInstruction>(i->inst) ||
//          dyn_cast<llvm::StoreInst>(i->inst) ||
//          dyn_cast<llvm::CmpInst>(i->inst)) {
//        unsigned int j = 0;
//        while (j < i->inst->getNumOperands()) {
//          llvm::Value *operand = i->inst->getOperand(j);
//          if ((!isa<llvm::Constant>(operand) ||
//               isa<llvm::GlobalValue>(operand)) &&
//              markedVariables.find(operand) == markedVariables.end()) {
//            markedVariables.insert(operand);
//          }
//          j++;
//        }
//      } else {
//        switch (i->inst->getOpcode()) {
//        case llvm::Instruction::Br: {
//          llvm::BranchInst *bi = cast<llvm::BranchInst>(i->inst);
//          if (bi->isUnconditional()) {
//            klee_error("Unconditional BR should not be marked in WP!");
//          } else {
//            markedVariables.insert(bi->getCondition());
//          }
//          break;
//        }
//        case llvm::Instruction::Call: {
//          // Interprocedural Marking not implemented yet!
//          // At the current moment it is not needed.
//          break;
//        }
//        default: {
//          i->inst->dump();
//          klee_error("Marking not implemented for this instruction yet!");
//        }
//        }
//      }
//    } else if ((*it).second == 2) {
//      // Marking not implemented for false dependency in instruction yet!
//      // At the current moment it is not needed.
//    }
//  }
//
//  // Printing reverseInstructionList will be omitted in the final commit
//  /*for (std::vector<std::pair<KInstruction *, int> >::const_reverse_iterator
//           it = reverseInstructionList.rbegin(),
//           ie = reverseInstructionList.rend();
//       it != ie; ++it) {
//    (*it).first->inst->dump();
//    llvm::errs() << " " << (*it).second << "\n";
//  }*/
//  return reverseInstructionList;
//}
//
// ref<Expr> TxWeakestPreCondition::GenerateWP(
//    std::vector<std::pair<KInstruction *, int> > reverseInstructionList,
//    bool markAllFlag) {
//
//  if (debugSubsumptionLevel >= 4)
//    klee_message("**********WP Interpolant Start************");
//  for (std::vector<std::pair<KInstruction *, int> >::const_reverse_iterator it
// =
//      reverseInstructionList.rbegin(), ie = reverseInstructionList.rend();
//      it != ie; ++it) {
//    llvm::Instruction *i = (*it).first->inst;
//    if ((*it).second == 1 || markAllFlag == true) {
//      // Retrieve the instruction
//      if (debugSubsumptionLevel >= 4) {
//        klee_message("Printing LLVM Instruction: ");
//        i->dump();
//        klee_message("---------------------------------------------");
//      }
//
//      switch (i->getOpcode()) {
//
//      case llvm::Instruction::Br: {
//        llvm::BranchInst *bi = cast<llvm::BranchInst>(i);
//        if (bi->isUnconditional()) {
//          if (markAllFlag != true)
//            klee_error("Unconditional BR is not marked in WP!");
//          // else
//          // Nothing is needed to be done	.
//        } else {
//          // llvm::Value* cond = bi->getCondition();
//          // Nothing specific is needed to be done for now.
//        }
//        break;
//      }
//
//      case llvm::Instruction::FCmp:
//      case llvm::Instruction::ICmp: {
//        if (markAllFlag == true && !isTargetDependent(i, this->WPExpr)) {
//          break;
//        }
//
//        // Getting the expressions from the left and right operand
//        ref<Expr> left = this->generateExprFromOperand(i, 0);
//        ref<Expr> right = this->generateExprFromOperand(i, 1);
//        ref<Expr> result;
//        // second step is to Storing the updated WP expression
//        llvm::CmpInst *ICC = dyn_cast<llvm::CmpInst>(i);
//        switch (ICC->getPredicate()) {
//        case llvm::CmpInst::ICMP_EQ:
//          result = EqExpr::create(left, right);
//          break;
//        case llvm::CmpInst::ICMP_NE:
//          result = NeExpr::create(left, right);
//          break;
//        case llvm::CmpInst::ICMP_UGT:
//          result = UgtExpr::create(left, right);
//          break;
//        case llvm::CmpInst::ICMP_UGE:
//          result = UgeExpr::create(left, right);
//          break;
//        case llvm::CmpInst::ICMP_ULT:
//          result = UltExpr::create(left, right);
//          break;
//        case llvm::CmpInst::ICMP_ULE:
//          result = UleExpr::create(left, right);
//          break;
//        case llvm::CmpInst::ICMP_SGT:
//          result = SgtExpr::create(left, right);
//          break;
//        case llvm::CmpInst::ICMP_SGE:
//          result = SgeExpr::create(left, right);
//          break;
//        case llvm::CmpInst::ICMP_SLT:
//          result = SltExpr::create(left, right);
//          break;
//        case llvm::CmpInst::ICMP_SLE:
//          result = SleExpr::create(left, right);
//          break;
//          // todo Handle Floating Point
//        case llvm::CmpInst::FCMP_FALSE:
//          klee_error("FCMP_FALSE not implemented yet!");
//          break;
//        case llvm::CmpInst::FCMP_OEQ:
//          klee_error("FCMP_OEQ not implemented yet!");
//          break;
//        case llvm::CmpInst::FCMP_OGT:
//          klee_error("FCMP_OGT not implemented yet!");
//          break;
//        case llvm::CmpInst::FCMP_OGE:
//          klee_error("FCMP_OGE not implemented yet!");
//          break;
//        case llvm::CmpInst::FCMP_OLT:
//          klee_error("FCMP_OLT not implemented yet!");
//          break;
//        case llvm::CmpInst::FCMP_OLE:
//          klee_error("FCMP_OLE not implemented yet!");
//          break;
//        case llvm::CmpInst::FCMP_ONE:
//          klee_error("FCMP_ONE not implemented yet!");
//          break;
//        case llvm::CmpInst::FCMP_ORD:
//          klee_error("FCMP_ORD not implemented yet!");
//          break;
//        case llvm::CmpInst::FCMP_UNO:
//          klee_error("FCMP_UNO not implemented yet!");
//          break;
//        case llvm::CmpInst::FCMP_UEQ:
//          klee_error("FCMP_UEQ not implemented yet!");
//          break;
//        case llvm::CmpInst::FCMP_UGT:
//          klee_error("FCMP_UGT not implemented yet!");
//          break;
//        case llvm::CmpInst::FCMP_UGE:
//          klee_error("FCMP_UGE not implemented yet!");
//          break;
//        case llvm::CmpInst::FCMP_ULT:
//          klee_error("FCMP_ULT not implemented yet!");
//          break;
//        case llvm::CmpInst::FCMP_ULE:
//          klee_error("FCMP_ULE not implemented yet!");
//          break;
//        case llvm::CmpInst::FCMP_UNE:
//          klee_error("FCMP_UNE not implemented yet!");
//          break;
//        case llvm::CmpInst::FCMP_TRUE:
//          klee_error("FCMP_TRUE not implemented yet!");
//          break;
//        case llvm::CmpInst::BAD_FCMP_PREDICATE:
//          klee_error("BAD_FCMP_PREDICATE not implemented yet!");
//          break;
//        case llvm::CmpInst::BAD_ICMP_PREDICATE:
//          klee_error("BAD_ICMP_PREDICATE not implemented yet!");
//          break;
//        }
//
//        this->updateWPExpr(result);
//        break;
//      }
//
//      case llvm::Instruction::FAdd:
//      case llvm::Instruction::Add:
//      case llvm::Instruction::Sub:
//      case llvm::Instruction::FSub:
//      case llvm::Instruction::Mul:
//      case llvm::Instruction::FMul:
//      case llvm::Instruction::FDiv:
//      case llvm::Instruction::UDiv:
//      case llvm::Instruction::SDiv:
//      case llvm::Instruction::URem:
//      case llvm::Instruction::SRem:
//      case llvm::Instruction::And:
//      case llvm::Instruction::Or:
//      case llvm::Instruction::Xor:
//      case llvm::Instruction::Shl:
//      case llvm::Instruction::LShr:
//      case llvm::Instruction::AShr: {
//        if (markAllFlag == true && !isTargetDependent(i, this->WPExpr)) {
//          break;
//        }
//        // Getting the expressions from the left and right operand
//        ref<Expr> left = this->generateExprFromOperand(i, 0);
//        ref<Expr> right = this->generateExprFromOperand(i, 1);
//
//        ref<Expr> rhs;
//        switch (i->getOpcode()) {
//        case llvm::Instruction::Add:
//          rhs = AddExpr::create(left, right);
//          break;
//        case llvm::Instruction::Sub:
//          rhs = SubExpr::create(left, right);
//          break;
//        case llvm::Instruction::Mul:
//          rhs = MulExpr::create(left, right);
//          break;
//        case llvm::Instruction::UDiv:
//          rhs = UDivExpr::create(left, right);
//          break;
//        case llvm::Instruction::SDiv:
//          rhs = SDivExpr::create(left, right);
//          break;
//        case llvm::Instruction::URem:
//          rhs = URemExpr::create(left, right);
//          break;
//        case llvm::Instruction::SRem:
//          rhs = SRemExpr::create(left, right);
//          break;
//        case llvm::Instruction::And:
//          rhs = AndExpr::create(left, right);
//          break;
//        case llvm::Instruction::Or:
//          rhs = OrExpr::create(left, right);
//          break;
//        case llvm::Instruction::Xor:
//          rhs = XorExpr::create(left, right);
//          break;
//        case llvm::Instruction::Shl:
//          rhs = ShlExpr::create(left, right);
//          break;
//        case llvm::Instruction::LShr:
//          rhs = LShrExpr::create(left, right);
//          break;
//        case llvm::Instruction::AShr:
//          rhs = AShrExpr::create(left, right);
//          break;
//        }
//
//        ref<Expr> lhs = this->getLHS(i);
//        ref<Expr> result = EqExpr::create(lhs, rhs);
//        this->updateWPExpr(result);
//        break;
//      }
//
//      case llvm::Instruction::Load: {
//        // Do nothing, Load instructions are handled by the
//        // generateExprFromOperand
//        // function in binary operations
//        break;
//      }
//
//      case llvm::Instruction::Store: {
//        if (markAllFlag == true
//            && !isTargetDependent(i->getOperand(1), this->WPExpr)) {
//          break;
//        }
//        ref<Expr> left = this->generateExprFromOperand(i, 0);
//        ref<Expr> right = this->generateExprFromOperand(i, 1);
//        ref<Expr> result = EqExpr::create(right, left);
//        this->updateWPExpr(result);
//        break;
//      }
//
//      case llvm::Instruction::Call: {
//        if (markAllFlag == true && !isTargetDependent(i, this->WPExpr)) {
//          break;
//        }
//
//        llvm::CallInst *call = dyn_cast<llvm::CallInst>(i);
//
//        if (call->getCalledFunction()->getName() == "klee_assume") {
//          // Nothing specific is needed to be done for now.
//        } else if (call->getCalledFunction()->getName()
//            == "klee_make_symbolic") {
//          // Nothing specific is needed to be done for now.
//        } else {
//          if (call->doesNotReturn()) {
//            klee_error("Call Instructions without return value are not yet "
//                "implemented.");
//          } else {
//            llvm::Function *CalledFunc = call->getCalledFunction();
//            llvm::Function::ArgumentListType &args =
//                CalledFunc->getArgumentList();
//            llvm::Function::ArgumentListType::iterator firstArg =
// args.begin();
//            llvm::Function::ArgumentListType::iterator lastArg = args.end();
//            uint64_t i = 0;
//            for (; firstArg != lastArg && i < call->getNumOperands();
//                ++firstArg, i++) {
//              llvm::Value *funcArg = dyn_cast<llvm::Value>(firstArg);
//              this->WPExpr = replaceCallArguments(this->WPExpr, funcArg,
//                  call->getOperand(i));
//            }
//            klee_error(
//                "Call Instructions with return value are not yet
// implemented.");
//          }
//        }
//        break;
//      }
//
//      case llvm::Instruction::ZExt:
//      case llvm::Instruction::SExt:
//      case llvm::Instruction::Trunc:
//      case llvm::Instruction::BitCast: {
//        // Getting the expressions from the operand
//        ref<Expr> operand = this->generateExprFromOperand(i, 0);
//        if (markAllFlag == true && !isTargetDependent(i, this->WPExpr)) {
//          break;
//        }
//        ref<Expr> lhs = this->getLHS(i);
//        ref<Expr> result = EqExpr::create(lhs, operand);
//        this->updateWPExpr(result);
//        break;
//      }
//
//      case llvm::Instruction::FPToSI:
//      case llvm::Instruction::SIToFP:
//      case llvm::Instruction::Alloca: {
//        // Nothing specific is needed to be done for now.
//        break;
//      }
//
//      case llvm::Instruction::GetElementPtr: {
//        if (markAllFlag == true && !isTargetDependent(i, this->WPExpr)) {
//          break;
//        }
//        klee_error("GetElementPtr Instruction is not yet implemented.");
//      }
//
//      case llvm::Instruction::Ret: {
//        if (markAllFlag == true && !isTargetDependent(i, this->WPExpr)) {
//          break;
//        }
//        klee_error("Ret Instruction is not yet implemented.");
//      }
//
//      case llvm::Instruction::Switch: {
//        llvm::SwitchInst *si = cast<llvm::SwitchInst>(i);
//        if (markAllFlag == true
//            && !isTargetDependent(si->getCondition(), this->WPExpr)) {
//          break;
//        }
//        klee_error("Switch Instruction is not yet implemented.");
//      }
//
//      default: {
//        klee_message("+++++++++++++++++++++++++++++++++++++++++++++");
//        klee_message("LLVM Instruction Not Implemeneted Yet: ");
//        i->dump();
//        klee_error("+++++++++++++++++++++++++++++++++++++++++++++");
//      }
//      }
//      if (debugSubsumptionLevel >= 4) {
//        klee_message("**** Weakest PreCondition At Each Instruction ****");
//        WPExpr->dump();
//        klee_message("***************************************");
//      }
//    } else if ((*it).second == 2) {
//      klee_message("False case of LLVM Instruction Not Implemeneted Yet");
//      i->dump();
//    }
//  }
//
//  if (debugSubsumptionLevel >= 3) {
//    klee_message("***************************************");
//    klee_message("******** Weakest PreCondition *********");
//    WPExpr->dump();
//    klee_message("***************************************");
//  }
//
//  if (debugSubsumptionLevel >= 4)
//    klee_message("**********Generating WP finished**********");
//
//  return WPExpr;
//}

// ref<Expr> TxWeakestPreCondition::replaceCallArguments(ref<Expr> interpolant,
//                                                      llvm::Value *funcArg,
//                                                      llvm::Value *callArg) {
//  switch (interpolant->getKind()) {
//  case Expr::InvalidKind:
//  case Expr::Constant: { return interpolant; }
//
//  case Expr::Read:
//  case Expr::Concat: {
//    llvm::Value *array = TxWPArrayStore::getValuePointer(interpolant);
//    if (array == funcArg) {
//      std::string arrayName = callArg->getName();
//      const std::string ext(".addr");
//      if (arrayName.find(ext))
//        arrayName = arrayName.substr(0, arrayName.size() - ext.size());
//      const Array *symArray =
// TxShadowArray::getSymbolicShadowArray(arrayName);
//      llvm::errs() << symArray->getName();
//
//      if (symArray != NULL) {
//        ref<Expr> Res(0);
//        unsigned NumBytes = symArray->getDomain() / 8;
//        assert(symArray->getDomain() == NumBytes * 8 && "Invalid read size!");
//        for (unsigned i = 0; i != NumBytes; ++i) {
//          unsigned idx =
//              Context::get().isLittleEndian() ? i : (NumBytes - i - 1);
//          ref<Expr> Byte =
//              ReadExpr::create(UpdateList(symArray, 0),
//                               ConstantExpr::alloc(idx,
// symArray->getDomain()));
//          Res = i ? ConcatExpr::create(Byte, Res) : Byte;
//        }
//        klee_error(
//            "TxWeakestPreCondition::replaceCallArguments Not tested yet");
//        return Res;
//      } else {
//        interpolant->dump();
//        klee_error("TxWeakestPreCondition::replaceCallArguments Shadow array "
//                   "doesn't exist!");
//      }
//    }
//    return interpolant;
//  }
//
//  case Expr::NotOptimized:
//  case Expr::Not:
//  case Expr::Extract:
//  case Expr::ZExt:
//  case Expr::SExt: {
//    ref<Expr> kids[1];
//    kids[0] = replaceCallArguments(interpolant->getKid(0), funcArg, callArg);
//    return interpolant->rebuild(kids);
//  }
//
//  case Expr::Eq:
//  case Expr::Ne:
//  case Expr::Ult:
//  case Expr::Ule:
//  case Expr::Ugt:
//  case Expr::Uge:
//  case Expr::Slt:
//  case Expr::Sle:
//  case Expr::Sgt:
//  case Expr::Sge:
//  case Expr::LastKind:
//  case Expr::Add:
//  case Expr::Sub:
//  case Expr::Mul:
//  case Expr::UDiv:
//  case Expr::SDiv:
//  case Expr::URem:
//  case Expr::SRem:
//  case Expr::And:
//  case Expr::Or:
//  case Expr::Xor:
//  case Expr::Shl:
//  case Expr::LShr:
//  case Expr::AShr: {
//    ref<Expr> kids[2];
//    kids[0] = replaceCallArguments(interpolant->getKid(0), funcArg, callArg);
//    kids[1] = replaceCallArguments(interpolant->getKid(1), funcArg, callArg);
//    return interpolant->rebuild(kids);
//  }
//
//  case Expr::Select: {
//    ref<Expr> kids[3];
//    kids[0] = replaceCallArguments(interpolant->getKid(0), funcArg, callArg);
//    kids[1] = replaceCallArguments(interpolant->getKid(1), funcArg, callArg);
//    kids[2] = replaceCallArguments(interpolant->getKid(2), funcArg, callArg);
//    return interpolant->rebuild(kids);
//  }
//  }
//  // Sanity check
//  klee_error("Control should not reach here in "
//             "TxWeakestPreCondition::replaceCallArguments");
//  return interpolant;
//}

// ref<Expr> TxWeakestPreCondition::getLHS(llvm::Instruction *i) {
//  ref<Expr> lhs = dependency->getAddress(i, &TxWPArrayStore::ac,
//                                         TxWPArrayStore::array, this);
//  return lhs;
//}
//
// void TxWeakestPreCondition::updateWPExpr(ref<Expr> result) {
//  if (WPExpr == eb->False()) {
//    WPExpr = result;
//  } else {
//    this->substituteExpr(result);
//    this->simplifyWPExpr();
//  }
//}
//
// void TxWeakestPreCondition::substituteExpr(ref<Expr> result) {
//  switch (result->getKind()) {
//  case Expr::Constant: {
//    // Nothing is needed to be done, it's either true or false
//    break;
//  }
//  case Expr::Eq: {
//    ref<Expr> lhs = result->getKid(0);
//    ref<Expr> rhs = result->getKid(1);
//    if (isa<ConstantExpr>(rhs)) {
//      ref<Expr> temp = lhs;
//      lhs = rhs;
//      rhs = temp;
//    }
//
//    WPExpr = this->substituteExpr(WPExpr, lhs, rhs);
//    break;
//  }
//  default: {
//    result->dump();
//    klee_error("Substitution for this expressions is not defined yet!");
//  }
//  }
//}
//
// ref<Expr> TxWeakestPreCondition::substituteExpr(ref<Expr> base,
//    const ref<Expr> lhs, const ref<Expr> rhs) {
//  if (base.compare(lhs) == 0)
//    return rhs;
//  else if (base.compare(rhs) == 0)
//    return lhs;
//  else {
//    switch (base->getKind()) {
//    case Expr::InvalidKind:
//    case Expr::Constant: {
//      return base;
//    }
//
//    case Expr::NotOptimized:
//    case Expr::Read:
//    case Expr::Not:
//    case Expr::Extract:
//    case Expr::ZExt:
//    case Expr::SExt: {
//      ref<Expr> kids[1];
//      kids[0] = this->substituteExpr(base->getKid(0), lhs, rhs);
//      return base->rebuild(kids);
//    }
//
//    case Expr::Concat:
//    case Expr::Eq:
//    case Expr::Ne:
//    case Expr::Ult:
//    case Expr::Ule:
//    case Expr::Ugt:
//    case Expr::Uge:
//    case Expr::Slt:
//    case Expr::Sle:
//    case Expr::Sgt:
//    case Expr::Sge:
//    case Expr::LastKind:
//    case Expr::Add:
//    case Expr::Sub:
//    case Expr::Mul:
//    case Expr::UDiv:
//    case Expr::SDiv:
//    case Expr::URem:
//    case Expr::SRem:
//    case Expr::And:
//    case Expr::Or:
//    case Expr::Xor:
//    case Expr::Shl:
//    case Expr::LShr:
//    case Expr::AShr: {
//      ref<Expr> kids[2];
//      kids[0] = this->substituteExpr(base->getKid(0), lhs, rhs);
//      kids[1] = this->substituteExpr(base->getKid(1), lhs, rhs);
//      return base->rebuild(kids);
//    }
//
//    case Expr::Select: {
//      ref<Expr> kids[3];
//      kids[0] = this->substituteExpr(base->getKid(0), lhs, rhs);
//      kids[1] = this->substituteExpr(base->getKid(1), lhs, rhs);
//      kids[2] = this->substituteExpr(base->getKid(1), lhs, rhs);
//      return base->rebuild(kids);
//    }
//    }
//  }
//  // Sanity check
//  klee_error(
//      "Control should not reach here in
// TxWeakestPreCondition::substituteExpr!");
//  return base;
//}
//
// void TxWeakestPreCondition::simplifyWPExpr() {
//
//  switch (WPExpr->getKind()) {
//  case Expr::Eq:
//  case Expr::Ne:
//  case Expr::Ult:
//  case Expr::Ule:
//  case Expr::Ugt:
//  case Expr::Uge:
//  case Expr::Slt:
//  case Expr::Sle:
//  case Expr::Sgt:
//  case Expr::Sge: {
//    ref<Expr> kids[2];
//    kids[0] = WPExpr->getKid(0);
//    kids[1] = WPExpr->getKid(1);
//    std::map<ref<Expr>, uint64_t> *newLinearTerm = new std::map<ref<Expr>,
//        uint64_t>;
//    if (isa<ConstantExpr>(kids[1])) {
//      ref<ConstantExpr> constant = dyn_cast<ConstantExpr>(kids[1]);
//      insertTerm(newLinearTerm, constant->getZExtValue(),
//          TxWPArrayStore::constValues);
//    } else {
//      newLinearTerm = this->simplifyWPTerm(newLinearTerm, kids[1]);
//    }
//    newLinearTerm = this->simplifyWPTerm(newLinearTerm, kids[0]);
//    convertToExpr(newLinearTerm);
//
//    delete newLinearTerm;
//    break;
//  }
//  case Expr::Constant: {
//    // Do nothing. The expression is in the form of True or False
//    break;
//  }
//
//  default: {
//    klee_message("Error while parsing WP Expression:");
//    WPExpr->dump();
//    klee_error("All WP Expressions should be in the form LinearTerm CMP "
//        "Constant. Ex. X + 2Y < 5");
//  }
//  }
//}
//
// std::map<ref<Expr>, uint64_t> *TxWeakestPreCondition::simplifyWPTerm(
//    std::map<ref<Expr>, uint64_t> *newLinearTerm, ref<Expr> linearTerm) {
//  if (isa<ConstantExpr>(linearTerm)) {
//    ref<ConstantExpr> constant = dyn_cast<ConstantExpr>(linearTerm);
//    insertTerm(newLinearTerm, (-1) * constant->getZExtValue(),
//        TxWPArrayStore::constValues);
//  } else {
//    switch (linearTerm->getKind()) {
//    case Expr::Concat:
//    case Expr::Read: {
//      insertTerm(newLinearTerm, 1, linearTerm);
//      break;
//    }
//    case Expr::Add:
//    case Expr::Sub: {
//      ref<Expr> kids[2];
//      kids[0] = linearTerm->getKid(0);
//      simplifyWPTerm(newLinearTerm, kids[0]);
//      kids[1] = linearTerm->getKid(1);
//      simplifyWPTerm(newLinearTerm, kids[1]);
//      break;
//    }
//    case Expr::Mul:
//    case Expr::UDiv:
//    case Expr::SDiv: {
//      ref<Expr> kids[2];
//      kids[0] = linearTerm->getKid(0);
//      kids[1] = linearTerm->getKid(1);
//      if (isa<ConstantExpr>(kids[0]) && isa<ReadExpr>(kids[1])) {
//        ref<ConstantExpr> coeff = dyn_cast<ConstantExpr>(kids[0]);
//        insertTerm(newLinearTerm, coeff->getZExtValue(), kids[1]);
//      } else {
//        klee_message(
//            "Error while parsing WP Expression. Not in canonical form:");
//        linearTerm->dump();
//        klee_error("The Coefficient should come first. Ex. 2*M");
//      }
//      break;
//    }
//    default: {
//      linearTerm->dump();
//      klee_error("LHS simplification for this term is not implemented yet");
//    }
//    }
//  }
//  return newLinearTerm;
//}
//
// void TxWeakestPreCondition::insertTerm(
//    std::map<ref<Expr>, uint64_t> *newLinearTerm, uint64_t coeff,
//    const ref<Expr> variable) {
//  std::map<ref<Expr>, uint64_t>::iterator it = newLinearTerm->find(variable);
//  if (it == newLinearTerm->end())
//    newLinearTerm->insert(std::pair<ref<Expr>, uint64_t>(variable, coeff));
//  else
//    it->second = it->second + coeff;
//}
//
// void TxWeakestPreCondition::convertToExpr(
//    std::map<ref<Expr>, uint64_t> *newLinearTerm) {
//  ref<Expr> kids[2];
//  ref<Expr> temp = eb->False();
//  for (std::map<ref<Expr>, uint64_t>::const_iterator it =
//      newLinearTerm->begin(), ie = newLinearTerm->end(); it != ie; ++it) {
//    if (it->first == TxWPArrayStore::constValues) {
//      kids[1] = ConstantExpr::create(it->second, Expr::Int32);
//    } else {
//      ref<Expr> lhs;
//      if (it->second == 1) {
//        lhs = it->first;
//      } else {
//        lhs = MulExpr::create(ConstantExpr::create(it->second, Expr::Int32),
//            it->first);
//      }
//      if (temp == eb->False()) {
//        temp = lhs;
//      } else {
//        temp = AddExpr::create(lhs, temp);
//      }
//    }
//  }
//  kids[0] = temp;
//  WPExpr = WPExpr->rebuild(kids);
//}

ref<Expr> TxWeakestPreCondition::intersectExpr(
    ref<Expr> branchCondition, ref<Expr> expr1, ref<Expr> expr2,
    ref<Expr> interpolant, std::set<const Array *> existentials,
    TxStore::LowerInterpolantStore concretelyAddressedHistoricalStore,
    TxStore::LowerInterpolantStore symbolicallyAddressedHistoricalStore,
    TxStore::TopInterpolantStore concretelyAddressedStore,
    TxStore::TopInterpolantStore symbolicallyAddressedStore) {

  //  llvm::outs() << "\nbranchCondition - expr1 - expr2 - interpolant\n";
  //  if (!branchCondition.isNull())
  //    branchCondition->dump();
  //  llvm::outs() << "\n--------------\n";
  //  if (!expr1.isNull())
  //    expr1->dump();
  //  llvm::outs() << "\n--------------\n";
  //  if (!expr2.isNull())
  //    expr2->dump();
  //  llvm::outs() << "\n--------------\n";
  //  if (!interpolant.isNull())
  //    interpolant->dump();
  //  llvm::outs() << "\n===============\n";

  std::vector<Partition<ref<TxAllocationContext> > > conAddStoreParts =
      TxPartitionHelper::partitionConAddStoreOnCond(branchCondition,
                                                    concretelyAddressedStore);
  //  llvm::outs() << "\n------concrete address store partitions-------\n";
  //  branchCondition->dump();
  //  for (unsigned int i = 0; i < conAddStoreParts.size(); i++) {
  //    conAddStoreParts.at(i).print();
  //    llvm::outs() << "\n-------------\n";
  //  }
  //  llvm::outs() << "\n===============\n";
  //  llvm::outs() << "\n------start deleting address store partitions size = "
  //               << concretelyAddressedStore.size() << "\n";
  for (TxStore::TopInterpolantStore::const_iterator
           mapIt = concretelyAddressedStore.begin(),
           mapIe = concretelyAddressedStore.end();
       mapIt != mapIe; ++mapIt) {
    if (!(conAddStoreParts[0].exprs.find(mapIt->first) ==
          conAddStoreParts[0].exprs.end())) {
      concretelyAddressedStore.erase(mapIt->first);
    }
  }
  //  llvm::outs() << "\n------end deleting address store partitions size = "
  //               << concretelyAddressedStore.size() << "\n";

  // partition interpolant based on branchCondition
  std::vector<ref<Expr> > interpolantExprs;
  TxPartitionHelper::getExprsFromAndExpr(interpolant, interpolantExprs);
  std::vector<Partition<ref<Expr> > > interpolantParts =
      TxPartitionHelper::partitionExprsOnCond(branchCondition,
                                              interpolantExprs);

  //  llvm::outs() << "\n------interpolant partitions-------\n";
  //  for (unsigned int i = 0; i < interpolantParts.size(); i++) {
  //    interpolantParts.at(i).print();
  //    llvm::outs() << "\n-------------\n";
  //  }
  //  llvm::outs() << "\n===============\n";

  // partition w1 based on branchCondition
  std::vector<ref<Expr> > w1Exprs;
  TxPartitionHelper::getExprsFromAndExpr(expr1, w1Exprs);
  std::vector<Partition<ref<Expr> > > w1Parts =
      TxPartitionHelper::partitionExprsOnCond(branchCondition, w1Exprs);

  //  llvm::outs() << "\n------wp1 partitions-------\n";
  //  for (unsigned int i = 0; i < w1Parts.size(); i++) {
  //    w1Parts.at(i).print();
  //    llvm::outs() << "\n-------------\n";
  //  }
  //  llvm::outs() << "\n===============\n";

  // partition w2 based on branchCondition
  std::vector<ref<Expr> > w2Exprs;
  TxPartitionHelper::getExprsFromAndExpr(expr2, w2Exprs);
  std::vector<Partition<ref<Expr> > > w2Parts =
      TxPartitionHelper::partitionExprsOnCond(branchCondition, w2Exprs);

  //  llvm::outs() << "\n------wp2 partitions-------\n";
  //  for (unsigned int i = 0; i < w2Parts.size(); i++) {
  //    w2Parts.at(i).print();
  //    llvm::outs() << "\n-------------\n";
  //  }
  //  llvm::outs() << "\n===============\n";

  // Keep related part from interpolant and non-related parts from WP1 & WP2
  interpolantParts.at(1).exprs.insert(w1Parts.at(0).exprs.begin(),
                                      w1Parts.at(0).exprs.end());
  interpolantParts.at(1).exprs.insert(w2Parts.at(0).exprs.begin(),
                                      w2Parts.at(0).exprs.end());

  //  llvm::outs() << "\n------after intersection 1 -------\n";
  //  for (std::set<ref<Expr> >::const_iterator
  //           exprIt = interpolantParts.at(1).exprs.begin(),
  //           exprIe = interpolantParts.at(1).exprs.end();
  //       exprIt != exprIe; ++exprIt) {
  //    (*exprIt)->dump();
  //  }
  //  llvm::outs() << "\n===============\n";

  std::vector<ref<Expr> > tmpExprs =
      TxExprHelper::rangeSimplifyFromExprs(interpolantParts.at(1).exprs);
  //  std::set<ref<Expr> > tmpExprs = interpolantParts.at(1).exprs;
  ref<Expr> res = TxPartitionHelper::createAnd(tmpExprs);

  //  llvm::outs() << "\n------after intersection 2 -------\n";
  //  res->dump();
  //  llvm::outs() << "\n===============\n";

  return res;
}

std::map<std::string, ref<Expr> > TxWeakestPreCondition::extractExprs(
    TxStore::TopInterpolantStore concretelyAddressedStore) {
  std::map<std::string, ref<Expr> > res;
  for (TxStore::TopInterpolantStore::const_iterator
           topIs = concretelyAddressedStore.begin(),
           topIe = concretelyAddressedStore.end(), topIt = topIs;
       topIt != topIe; ++topIt) {
    std::string var(topIt->first->getValue()->getName().data());
    ref<Expr> value = topIt->second.begin()->second->getExpression();
    res.insert(std::pair<std::string, ref<Expr> >(var, value));
  }
  return res;
}

/*std::vector<ref<Expr> >
TxWeakestPreCondition::intersectExpr_aux(std::vector<ref<Expr> > expr1,
                                         std::vector<ref<Expr> > expr2) {
  if(expr1->getKind() == Expr::Sle && expr2->getKind() == Expr::Sle) {
   if (expr1->getKid(0) == expr2->getKid(0)){
   ref<Expr> kids[2];
   kids[0] = expr1->getKid(0);
   //sanity check
   assert(isa<ConstantExpr>(expr1->getKid(1)) &&
   "expr1->getKid(1) should be constant expression");
   assert(isa<ConstantExpr>(expr2->getKid(1)) &&
   "expr2->getKid(1) should be constant expression");
   kids[1] =
   this->getMinOfConstExpr(dyn_cast<ConstantExpr>(expr1->getKid(1)),dyn_cast<ConstantExpr>(expr2->getKid(1)));
   return expr1->rebuild(kids);
   }else{
   expr1->dump();
   expr2->dump();
   klee_error("TxWeakestPreCondition::intersectExpr left operands
   are not the same.");
   return AndExpr::create(expr1,expr2);
   }
   } else if (expr1->getKind() == Expr::Slt && expr2->getKind() == Expr::Slt) {
   if (expr1->getKid(0) == expr2->getKid(0)) {
   ref<Expr> kids[2];
   kids[0] = expr1->getKid(0);
   // sanity check
   assert(isa<ConstantExpr>(expr1->getKid(1)) &&
   "expr1->getKid(1) should be constant expression");
   assert(isa<ConstantExpr>(expr2->getKid(1)) &&
   "expr2->getKid(1) should be constant expression");
   kids[1] =
   this->getMinOfConstExpr(dyn_cast<ConstantExpr>(expr1->getKid(1)),
   dyn_cast<ConstantExpr>(expr2->getKid(1)));
   return expr1->rebuild(kids);
   } else {
   expr1->dump();
   expr2->dump();
   klee_error(
   "TxWeakestPreCondition::intersectExpr left operands are not the same.");
   return AndExpr::create(expr1, expr2);
   }
   }else{
   expr1->dump();
   expr2->dump();
   klee_error("TxWeakestPreCondition::intersectExpr for these expressions
   is not implemented yet.");
   return AndExpr::create(expr1,expr2);
   }
}*/

// ref<ConstantExpr>
// TxWeakestPreCondition::getMinOfConstExpr(ref<ConstantExpr> expr1,
//                                         ref<ConstantExpr> expr2) {
//  if ((expr1->getAPValue().getSExtValue() <
// expr2->getAPValue().getSExtValue()))
//    return expr1;
//  else
//    return expr2;
//}
//
// ref<ConstantExpr>
// TxWeakestPreCondition::getMaxOfConstExpr(ref<ConstantExpr> expr1,
//                                         ref<ConstantExpr> expr2) {
//  if (expr1.compare(expr2) <= 0)
//    return expr1;
//  else
//    return expr2;
//}

// bool TxWeakestPreCondition::isTargetDependent(llvm::Value *inst, ref<Expr>
// wp) {
//  switch (wp->getKind()) {
//  case Expr::InvalidKind:
//  case Expr::Constant: { return false; }
//
//  case Expr::Read: {
//    if (inst == TxWPArrayStore::getValuePointer(wp)) {
//      return true;
//    }
//    return false;
//  }
//
//  case Expr::Concat: {
//    if (inst == TxWPArrayStore::getValuePointer(
//                    TxWPArrayStore::getFunctionName(inst), wp)) {
//      return true;
//    }
//    return false;
//  }
//
//  case Expr::NotOptimized:
//  case Expr::Not:
//  case Expr::Extract:
//  case Expr::ZExt:
//  case Expr::SExt: {
//    ref<Expr> kids[1];
//    kids[0] = WPExpr->getKid(0);
//    return isTargetDependent(inst, kids[0]);
//  }
//
//  case Expr::Eq:
//  case Expr::Ne:
//  case Expr::Ult:
//  case Expr::Ule:
//  case Expr::Ugt:
//  case Expr::Uge:
//  case Expr::Slt:
//  case Expr::Sle:
//  case Expr::Sgt:
//  case Expr::Sge:
//  case Expr::LastKind:
//  case Expr::Add:
//  case Expr::Sub:
//  case Expr::Mul:
//  case Expr::UDiv:
//  case Expr::SDiv:
//  case Expr::URem:
//  case Expr::SRem:
//  case Expr::And:
//  case Expr::Or:
//  case Expr::Xor:
//  case Expr::Shl:
//  case Expr::LShr:
//  case Expr::AShr: {
//    ref<Expr> kids[2];
//    kids[0] = WPExpr->getKid(0);
//    kids[1] = WPExpr->getKid(1);
//    return (isTargetDependent(inst, kids[0]) ||
//            isTargetDependent(inst, kids[1]));
//  }
//
//  case Expr::Select: {
//    ref<Expr> kids[3];
//    kids[0] = WPExpr->getKid(0);
//    kids[1] = WPExpr->getKid(1);
//    kids[2] = WPExpr->getKid(2);
//    return (isTargetDependent(inst, kids[0]) ||
//            isTargetDependent(inst, kids[1]) ||
//            isTargetDependent(inst, kids[2]));
//  }
//  }
//  // Sanity check
//  klee_error("Control should not reach here in "
//             "TxWeakestPreCondition::isTargetDependent!");
//  return false;
//}

// =========================================================================
// Instantiating WP Expression at Subsumption Point
// =========================================================================

ref<Expr> TxWeakestPreCondition::instantiateWPExpression(
    TxDependency *dependency, ref<Expr> singleWPExpr, TxWPArrayStore *wpStore) {

  ref<Expr> dummy = ConstantExpr::create(0, Expr::Bool);
  switch (singleWPExpr->getKind()) {
  case Expr::InvalidKind:
  case Expr::Constant: {
    return singleWPExpr;
  }

  case Expr::Read: {
    ref<TxAllocationContext> address = wpStore->getAddress(singleWPExpr);
    if (address.isNull()) {
      singleWPExpr->dump();
      klee_error(
          "TxWeakestPreCondition::instantiateWPExpression address is null");
    }
    ref<Expr> storeValue = dependency->getLatestValueOfAddress(address);
    if (storeValue == dummy) {
      return singleWPExpr;
    }
    return storeValue;
  }

  case Expr::Concat: {
    ref<TxAllocationContext> address = wpStore->getAddress(singleWPExpr);
    if (address.isNull()) {
      singleWPExpr->dump();
      klee_error(
          "TxWeakestPreCondition::instantiateWPExpression address is null");
    }
    ref<Expr> storeValue = dependency->getLatestValueOfAddress(address);
    if (storeValue == dummy) {
      return singleWPExpr;
    }
    return storeValue;
  }

  case Expr::NotOptimized:
  case Expr::Not:
  case Expr::Extract:
  case Expr::ZExt:
  case Expr::SExt: {
    ref<Expr> kids[1];
    kids[0] =
        instantiateWPExpression(dependency, singleWPExpr->getKid(0), wpStore);
    return singleWPExpr->rebuild(kids);
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

    kids[0] =
        instantiateWPExpression(dependency, singleWPExpr->getKid(0), wpStore);
    kids[1] =
        instantiateWPExpression(dependency, singleWPExpr->getKid(1), wpStore);
    //    llvm::outs() << "----\n";
    //    singleWPExpr->dump();
    //    singleWPExpr->getKid(0)->dump();
    //    singleWPExpr->getKid(1)->dump();
    //    kids[0]->dump();
    //    kids[1]->dump();
    //    llvm::outs() << "----end\n";

    return singleWPExpr->rebuild(kids);
  }

  case Expr::Select: {
    ref<Expr> kids[3];
    kids[0] =
        instantiateWPExpression(dependency, singleWPExpr->getKid(0), wpStore);
    kids[1] =
        instantiateWPExpression(dependency, singleWPExpr->getKid(1), wpStore);
    kids[2] =
        instantiateWPExpression(dependency, singleWPExpr->getKid(2), wpStore);
    return singleWPExpr->rebuild(kids);
  }
  }
  // Sanity check
  klee_error("Control should not reach here in "
             "TxWeakestPreCondition::instantiateWPExpression!");

  return singleWPExpr;
}

// =========================================================================
// Functions Updating the Subsumption Table Entry
// =========================================================================

// \brief The algorithm for merging the WP with the deletion interpolant:
// 1- Extract the variables (Read & Concat expressions) from WP
// 2- For each variable find the respective ref<TxAllocationContext> from
//    wpStore
// 3- Extract the LLVM::Value from TxAllocationContext (getValue() function)
// 4- Search the components in entry and keep only the ref<TxAllocationContext>
//    with the same LLVM::Value component and the longest callHistory size
//    (similar to  TxDependency::getAddressofLatestCopyLLVMValue).
//    The logic here is that if multiple copies of the same LLVM::Value
//    exists (like local variables of a recursive function), then the one
//    with the longest callHistory is the latest one and hence, corresponds
//    to the respective variable in WP.
// 5- Change the LowerInterpolantStore to read or concat Expr on the variable
//    (In future we might need to change the name of the var to _shadow_var).
// 6- Add the respective Array * for each variable from wp to existentials
// 7- Replace the expression in interpolant component of entry with the WP
//    expression.

TxSubsumptionTableEntry *TxWeakestPreCondition::updateSubsumptionTableEntry(
    TxSubsumptionTableEntry *entry) {

  ref<Expr> wp = entry->getWPInterpolant();
  // extract Arrays read expressions from wp
  std::set<const Array *> readArrays;
  TxExprHelper::extractArrays(wp, readArrays);

  // Adding Arrays of shadow version of read expressions
  std::set<const Array *> shadowArrays;
  for (std::set<const Array *>::iterator it = readArrays.begin(),
                                         ie = readArrays.end();
       it != ie; ++it) {
    const Array *sarr = TxShadowArray::getSymbolicShadowArray((*it)->getName());
    if (sarr != NULL)
      shadowArrays.insert(sarr);
  }

  // removing shadow version of vars in WP Expr from Existentials
  std::set<const Array *> newExistentials = entry->getExistentials();
  for (std::set<const Array *>::iterator iter = newExistentials.begin();
       iter != newExistentials.end();) {
    if (shadowArrays.find(*iter) != shadowArrays.end())
      newExistentials.erase(iter++);
    else
      ++iter;
  }
  entry->setExistentials(newExistentials);

  // get TxAllocationContexts for ReadExpr from wpStore
  // Only one of the variable or its shadow would have TxAllocationContexts
  std::map<const Array *, ref<TxAllocationContext> > exprToAllocContext;
  for (std::set<const Array *>::iterator exprIt = readArrays.begin(),
                                         exprIe = readArrays.end();
       exprIt != exprIe; ++exprIt) {
    // search TxAllocationContext & add to the map
    ref<TxAllocationContext> address = wpStore->getAddress(*exprIt);
    if (!address.isNull()) {
      ref<Expr> var = wpStore->getExpr(address);
      exprToAllocContext[*exprIt] = address;
    }
  }

  // removing vars in WP Expr from concretelyAddressedStore
  TxStore::TopInterpolantStore concretelyAddressedStore =
      entry->getConcretelyAddressedStore();
  // process concretelyAddressedStore based on each value
  for (std::map<const Array *, ref<TxAllocationContext> >::iterator
           e2AllocContextIt = exprToAllocContext.begin(),
           e2AllocContextIe = exprToAllocContext.end();
       e2AllocContextIt != e2AllocContextIe; ++e2AllocContextIt) {
    llvm::Value *val = e2AllocContextIt->second->getValue();
    // Find the entry to be deleted from concretelyAddressedStore
    // The entry with the same value and longest call history
    unsigned int longest = 0;
    bool inConcAddStore = false;
    TopInterpolantStore::iterator candidateToDelete;
    for (TopInterpolantStore::iterator
             concAddStoreIt = concretelyAddressedStore.begin(),
             concAddStoreIe = concretelyAddressedStore.end();
         concAddStoreIt != concAddStoreIe; ++concAddStoreIt) {
      if (concAddStoreIt->first->getValue() == val &&
          concAddStoreIt->first->getCallHistory().size() >= longest) {
        longest = concAddStoreIt->first->getCallHistory().size();
        inConcAddStore = true;
        candidateToDelete = concAddStoreIt;
      }
    }

    // Commenting this check, apparantly some WP expressions might not be
    // marked!!!
    /*if (!inConcAddStore && concretelyAddressedStore.size() > 0) {
      wp->dump();
      val->dump();
      entry->dump();
      llvm::errs() << "concretelyAddressedStore size:"
                   << concretelyAddressedStore.size() << "\n";
      klee_error("TxWeakestPreCondition::updateSubsumptionTableEntry: cannot "
                 "find TxAllocationContext in concretelyAddressedStore");
    } */

    if (inConcAddStore)
      concretelyAddressedStore.erase(candidateToDelete);
  }
  entry->setConcretelyAddressedStore(concretelyAddressedStore);

  // removing shadow version of vars in WP Expr from Existentials
  ref<Expr> interpolant = entry->getInterpolant();
  if (!interpolant.isNull()) {
    ref<Expr> newInterpolant =
        TxExprHelper::removeShadowExprs(interpolant, shadowArrays);
    entry->setInterpolant(newInterpolant);
  }

  if (entry->getConcretelyAddressedHistoricalStore().size() > 0 ||
      entry->getSymbolicallyAddressedHistoricalStore().size() > 0 ||
      entry->getSymbolicallyAddressedStore().size() > 0) {
    entry->dump();
    klee_error("TxWeakestPreCondition::updateSubsumptionTableEntry: "
               "ConcretelyAddressedHistoricalStore or "
               "SymbolicallyAddressedHistoricalStore or "
               "SymbolicallyAddressedStore are not empty.");
  }

  return entry;

  /*
   ref<Expr> interpolant = entry->getInterpolant();
   TxStore::LowerInterpolantStore concretelyAddressedHistoricalStore =
   entry->getConcretelyAddressedHistoricalStore();
   TxStore::LowerInterpolantStore symbolicallyAddressedHistoricalStore =
   entry->getSymbolicallyAddressedHistoricalStore();
   TxStore::TopInterpolantStore concretelyAddressedStore =
   entry->getConcretelyAddressedStore();
   TxStore::TopInterpolantStore symbolicallyAddressedStore =
   entry->getSymbolicallyAddressedStore();
   std::set<const Array *> existentials = entry->getExistentials();

   if (concretelyAddressedHistoricalStore.size() > 0 ||
   symbolicallyAddressedStore.size() > 0 ||
   symbolicallyAddressedHistoricalStore.size() > 0) {
   llvm::errs() << "Size of concretelyAddressedHistoricalStore: "
   << concretelyAddressedStore.size() << "\n";
   llvm::errs() << "Size of symbolicallyAddressedStore: "
   << concretelyAddressedStore.size() << "\n";
   llvm::errs() << "Size of symbolicallyAddressedHistoricalStore: "
   << concretelyAddressedStore.size() << "\n";
   klee_error(
   "TxWeakestPreCondition::updateSubsumptionTableEntry for this case "
   "is not implemented yet.");
   } else {
   // TODO: Should apply the algorithm above.
   TxStore::TopInterpolantStore newConcretelyAddressedStore =
   updateConcretelyAddressedStore(concretelyAddressedStore, wp);
   entry->setConcretelyAddressedStore(newConcretelyAddressedStore);
   //    ref<Expr> newInterpolant =
   //        updateInterpolant(interpolant, replaceArrayWithShadow(wp));
   //    std::set<const Array *> newExistentials =
   //        updateExistentials(existentials, wp);
   //    entry->setInterpolant(newInterpolant);
   //    entry->setExistentials(newExistentials);
   }
   if (debugSubsumptionLevel >= 4) {
   // For future reference
   if (!interpolant.isNull())
   interpolant->dump();

   concretelyAddressedStore = entry->getConcretelyAddressedStore();
   for (TopInterpolantStore::const_iterator
   it = concretelyAddressedStore.begin(),
   ie = concretelyAddressedStore.end();
   it != ie; ++it) {
   (*it).first->dump();
   LowerInterpolantStore temp = (*it).second;
   for (LowerInterpolantStore::const_iterator it2 = temp.begin(),
   ie2 = temp.end();
   it2 != ie2; ++it2) {
   (*it2).first->dump();
   (*it2).second->dump();
   }
   }
   for (TopInterpolantStore::const_iterator
   it = symbolicallyAddressedStore.begin(),
   ie = symbolicallyAddressedStore.end();
   it != ie; ++it) {
   (*it).first->dump();
   LowerInterpolantStore temp = (*it).second;
   for (LowerInterpolantStore::const_iterator it2 = temp.begin(),
   ie2 = temp.end();
   it2 != ie2; ++it2) {
   (*it2).first->dump();
   (*it2).second->dump();
   }
   }

   for (LowerInterpolantStore::const_iterator
   it = concretelyAddressedHistoricalStore.begin(),
   ie = concretelyAddressedHistoricalStore.end();
   it != ie; ++it) {
   (*it).first->dump();
   (*it).second->dump();
   }

   for (LowerInterpolantStore::const_iterator
   it = symbolicallyAddressedHistoricalStore.begin(),
   ie = symbolicallyAddressedHistoricalStore.end();
   it != ie; ++it) {
   (*it).first->dump();
   (*it).second->dump();
   }
   }
   return entry;
   */
}

TxStore::TopInterpolantStore
TxWeakestPreCondition::updateConcretelyAddressedStore(
    TxStore::TopInterpolantStore concretelyAddressedStore, ref<Expr> wp) {

  ref<Expr> var = getVarFromExpr(wp);

  llvm::Value *allocaVar = wpStore->getValuePointer(var);
  TopInterpolantStore::iterator candidateForRemove =
      concretelyAddressedStore.end();
  for (TopInterpolantStore::iterator it = concretelyAddressedStore.begin(),
                                     ie = concretelyAddressedStore.end();
       it != ie; ++it) {

    if ((*it).first->getValue() == allocaVar)
      candidateForRemove = it;
  }

  if (candidateForRemove != concretelyAddressedStore.end()) {
    concretelyAddressedStore.erase(candidateForRemove);
  }
  return concretelyAddressedStore;
}

ref<Expr> TxWeakestPreCondition::getVarFromExpr(ref<Expr> wp) {

  switch (wp->getKind()) {
  case Expr::InvalidKind:
  case Expr::Read:
  case Expr::Concat:
  case Expr::Constant: {
    return wp;
  }

  case Expr::NotOptimized:
  case Expr::Not:
  case Expr::Extract:
  case Expr::ZExt:
  case Expr::SExt: {
    ref<Expr> kids[1];
    kids[0] = getVarFromExpr(wp->getKid(0));
    return kids[0];
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
    kids[0] = getVarFromExpr(wp->getKid(0));
    kids[1] = getVarFromExpr(wp->getKid(1));
    if (isa<ReadExpr>(kids[0]) || isa<ConcatExpr>(kids[0]))
      return kids[0];
    else
      return kids[1];
  }

  case Expr::Select: {
    ref<Expr> kids[3];
    kids[0] = getVarFromExpr(wp->getKid(0));
    kids[1] = getVarFromExpr(wp->getKid(1));
    kids[2] = getVarFromExpr(wp->getKid(2));
    if (isa<ReadExpr>(kids[0]) || isa<ConcatExpr>(kids[0]))
      return kids[0];
    else if (isa<ReadExpr>(kids[1]) || isa<ConcatExpr>(kids[1]))
      return kids[1];
    else
      return kids[1];
  }
  }
  // Sanity check
  klee_error("Control should not reach here in"
             "TxWeakestPreCondition::getVarFromExpr");
  return wp;
}

ref<Expr> TxWeakestPreCondition::updateInterpolant(ref<Expr> interpolant,
                                                   ref<Expr> wp) {
  klee_error("TxWeakestPreCondition::updateInterpolant");
  if (interpolant.isNull())
    return wp;

  ref<Expr> var = getVarFromExpr(wp);
  ref<Expr> unrelatedFrame = extractUnrelatedFrame(interpolant, var);
  if (unrelatedFrame == wpStore->constValues)
    return wp;
  else
    return AndExpr::create(unrelatedFrame, wp);
}

ref<Expr> TxWeakestPreCondition::extractUnrelatedFrame(ref<Expr> interpolant,
                                                       ref<Expr> var) {
  klee_error("TxWeakestPreCondition::extractUnrelatedFrame");
  switch (interpolant->getKind()) {
  case Expr::InvalidKind:
  case Expr::Constant: {
    return interpolant;
  }

  case Expr::Read:
  case Expr::Concat: {
    if (interpolant == var)
      return wpStore->constValues;
    else
      return interpolant;
  }

  case Expr::NotOptimized:
  case Expr::Not:
  case Expr::Extract:
  case Expr::ZExt:
  case Expr::SExt: {
    ref<Expr> kids[1];
    kids[0] = extractUnrelatedFrame(interpolant->getKid(0), var);
    if (kids[0] == wpStore->constValues)
      return wpStore->constValues;
    else
      return interpolant->rebuild(kids);
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
  case Expr::Shl:
  case Expr::LShr:
  case Expr::AShr: {
    ref<Expr> kids[2];
    kids[0] = extractUnrelatedFrame(interpolant->getKid(0), var);
    kids[1] = extractUnrelatedFrame(interpolant->getKid(1), var);
    if (kids[0] == wpStore->constValues || kids[1] == wpStore->constValues) {
      return wpStore->constValues;
    } else {
      return interpolant->rebuild(kids);
    }
  }

  // pass the other one as frame
  case Expr::Or:
  case Expr::Xor:
  case Expr::And: {
    ref<Expr> kids[2];
    kids[0] = extractUnrelatedFrame(interpolant->getKid(0), var);
    kids[1] = extractUnrelatedFrame(interpolant->getKid(1), var);
    if (kids[0] == wpStore->constValues && kids[1] == wpStore->constValues)
      klee_error(
          "TxWeakestPreCondition::extractUnrelatedFrame This AND case is "
          "not implemented yet!");
    if (kids[0] == wpStore->constValues && !(kids[1] == wpStore->constValues)) {
      return kids[1];
    } else if (!(kids[0] == wpStore->constValues) &&
               kids[1] == wpStore->constValues) {
      return kids[0];
    } else {
      return interpolant->rebuild(kids);
    }
  }

  case Expr::Select: {
    ref<Expr> kids[3];
    kids[0] = extractUnrelatedFrame(interpolant->getKid(0), var);
    kids[1] = extractUnrelatedFrame(interpolant->getKid(1), var);
    kids[2] = extractUnrelatedFrame(interpolant->getKid(2), var);

    if (kids[0] == wpStore->constValues || kids[1] == wpStore->constValues ||
        kids[2] == wpStore->constValues)
      return wpStore->constValues;
    else
      return interpolant->rebuild(kids);
  }
  }
  // Sanity check
  klee_error("Control should not reach here in "
             "TxWeakestPreCondition::extractUnrelatedFrame");
  return interpolant;
}

ref<Expr> TxWeakestPreCondition::replaceArrayWithShadow(ref<Expr> interpolant) {
  klee_error("TxWeakestPreCondition::replaceArrayWithShadow");

  switch (interpolant->getKind()) {
  case Expr::InvalidKind:
  case Expr::Constant: {
    return interpolant;
  }

  case Expr::Read:
  case Expr::Concat: {
    llvm::Value *array = wpStore->getValuePointer(interpolant);
    std::string arrayName = array->getName();
    const std::string ext(".addr");
    if (arrayName.find(ext))
      arrayName = arrayName.substr(0, arrayName.size() - ext.size());
    const Array *symArray =
        TxShadowArray::getSymbolicShadowArray(array->getName());
    if (symArray != NULL) {
      ref<Expr> Res(0);
      unsigned NumBytes = symArray->getDomain() / 8;
      assert(symArray->getDomain() == NumBytes * 8 && "Invalid read size!");
      for (unsigned i = 0; i != NumBytes; ++i) {
        unsigned idx = Context::get().isLittleEndian() ? i : (NumBytes - i - 1);
        ref<Expr> Byte =
            ReadExpr::create(UpdateList(symArray, 0),
                             ConstantExpr::alloc(idx, symArray->getDomain()));
        Res = i ? ConcatExpr::create(Byte, Res) : Byte;
      }
      return Res;
    } else {
      interpolant->dump();
      klee_error("TxWeakestPreCondition::replaceArrayWithShadow Shadow array "
                 "doesn't exist!");
    }
  }

  case Expr::NotOptimized:
  case Expr::Not:
  case Expr::Extract:
  case Expr::ZExt:
  case Expr::SExt: {
    ref<Expr> kids[1];
    kids[0] = replaceArrayWithShadow(interpolant->getKid(0));
    return interpolant->rebuild(kids);
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
    kids[0] = replaceArrayWithShadow(interpolant->getKid(0));
    kids[1] = replaceArrayWithShadow(interpolant->getKid(1));
    return interpolant->rebuild(kids);
  }

  case Expr::Select: {
    ref<Expr> kids[3];
    kids[0] = replaceArrayWithShadow(interpolant->getKid(0));
    kids[1] = replaceArrayWithShadow(interpolant->getKid(1));
    kids[2] = replaceArrayWithShadow(interpolant->getKid(2));
    return interpolant->rebuild(kids);
  }
  }
  // Sanity check
  klee_error(
      "Control should not reach here in TxWeakestPreCondition::getVarFromExpr");
  return interpolant;
}

std::set<const Array *>
TxWeakestPreCondition::updateExistentials(std::set<const Array *> existentials,
                                          ref<Expr> wp) {
  klee_error("TxWeakestPreCondition::updateExistentials");

  switch (wp->getKind()) {
  case Expr::InvalidKind:
  case Expr::Constant: {
    return existentials;
  }

  case Expr::Read:
  case Expr::Concat: {
    llvm::Value *array = wpStore->getValuePointer(wp);
    std::string arrayName = array->getName();
    const std::string ext(".addr");
    if (arrayName.find(ext))
      arrayName = arrayName.substr(0, arrayName.size() - ext.size());
    const Array *symArray =
        TxShadowArray::getSymbolicShadowArray(array->getName());
    if (!symArray) {
      wp->dump();
      klee_error(
          "TxWeakestPreCondition::updateExistentials Shadow array doesn't "
          "exist!");
    }
    if (existentials.find(symArray) == existentials.end()) {
      existentials.insert(symArray);
    }
    return existentials;
  }

  case Expr::NotOptimized:
  case Expr::Not:
  case Expr::Extract:
  case Expr::ZExt:
  case Expr::SExt: {
    std::set<const Array *> newExistentials =
        updateExistentials(existentials, wp->getKid(0));
    return newExistentials;
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
    std::set<const Array *> newExistentials =
        updateExistentials(existentials, wp->getKid(0));
    std::set<const Array *> newExistentials2 =
        updateExistentials(newExistentials, wp->getKid(1));
    return newExistentials2;
  }

  case Expr::Select: {
    std::set<const Array *> newExistentials =
        updateExistentials(existentials, wp->getKid(0));
    std::set<const Array *> newExistentials2 =
        updateExistentials(newExistentials, wp->getKid(1));
    std::set<const Array *> newExistentials3 =
        updateExistentials(newExistentials2, wp->getKid(2));
    return newExistentials3;
  }
  }
  // Sanity check
  klee_error(
      "Control should not reach here in TxWeakestPreCondition::getVarFromExpr");
  return existentials;
}

// =========================================================================
// Updated Version of Weakest PreCondition
// =========================================================================

std::pair<TxWPArrayStore *, std::pair<ref<Expr>, ref<Expr> > >
TxWeakestPreCondition::mergeWPArrayStore(TxWPArrayStore *childArrayStore1,
                                         TxWPArrayStore *childArrayStore2,
                                         ref<Expr> childWPInterpolant1,
                                         ref<Expr> childWPInterpolant2) {

  for (ArrayStore::const_iterator it = childArrayStore2->arrayStore.begin(),
                                  ie = childArrayStore2->arrayStore.end();
       it != ie; ++it) {
    if (childArrayStore1->arrayStore.find(it->first) ==
        childArrayStore1->arrayStore.end())
      childArrayStore1->arrayStore.insert(*it);
    else {
      ref<ReadExpr> re;
      if (isa<ReadExpr>(it->second.second))
        re = dyn_cast<ReadExpr>(it->second.second);
      else
        re = TxWPHelper::ExtractReadExpr(it->second.second);

      ref<ReadExpr> re2;
      if (isa<ReadExpr>(
              childArrayStore1->arrayStore.find(it->first)->second.second))
        re2 = dyn_cast<ReadExpr>(
            childArrayStore1->arrayStore.find(it->first)->second.second);
      else
        re2 = TxWPHelper::ExtractReadExpr(
            childArrayStore1->arrayStore.find(it->first)->second.second);

      childWPInterpolant2 = TxWPHelper::substituteArray(
          childWPInterpolant2, re->getArray(), re2->getArray());
    }
  }
  return std::make_pair(childArrayStore1, std::make_pair(childWPInterpolant1,
                                                         childWPInterpolant2));
}

void TxWeakestPreCondition::sanityCheckWPArrayStore(
    TxWPArrayStore *childArrayStore, ref<Expr> childWPInterpolant) {
  std::set<ref<Expr> > varsSet =
      TxWPHelper::extractVariables(childWPInterpolant);
  for (std::set<ref<Expr> >::const_iterator it = varsSet.begin(),
                                            ie = varsSet.end();
       it != ie; ++it) {
    int flag = false;
    for (ArrayStore::const_iterator it2 = childArrayStore->arrayStore.begin(),
                                    ie2 = childArrayStore->arrayStore.end();
         it2 != ie2; ++it2) {
      ref<ReadExpr> re;
      if (isa<ReadExpr>((*it)))
        re = dyn_cast<ReadExpr>((*it));
      else
        re = TxWPHelper::ExtractReadExpr((*it));

      ref<ReadExpr> re2;
      if (isa<ReadExpr>(it2->second.second))
        re2 = dyn_cast<ReadExpr>(it2->second.second);
      else
        re2 = TxWPHelper::ExtractReadExpr(it2->second.second);

      if (re2->getArray() == re->getArray()) {
        flag = true;
        continue;
      }
    }
    if (flag == false) {
      llvm::errs() << "Missing Item:";
      (*it)->dump();
      llvm::errs() << "Available Items:\n";
      for (ArrayStore::const_iterator it2 = childArrayStore->arrayStore.begin(),
                                      ie2 = childArrayStore->arrayStore.end();
           it2 != ie2; ++it2) {
        it2->second.second->dump();
      }
      klee_error(
          "TxWeakestPreCondition::sanityCheckWPArrayStore - Sanity Check: var "
          "not found!");
    }
  }
}

/**
 * Push up expression to top of BB
 */
ref<Expr> TxWeakestPreCondition::PushUp(
    std::vector<std::pair<KInstruction *, int> > reverseInstructionList) {

  //    llvm::outs() << "--- Begin printing instruction list ---\n";
  //    for (std::vector<std::pair<KInstruction *, int> >::const_iterator
  //             it = reverseInstructionList.begin(),
  //             ie = reverseInstructionList.end();
  //         it != ie; ++it) {
  //      llvm::Instruction *i = (*it).first->inst;
  //      int flag = (*it).second;
  //      // instruction list
  //      i->dump();
  //      llvm::outs() << flag << "\n";
  //    }
  //    llvm::outs() << "--- End of printing instruction list ---\n";

  for (std::vector<std::pair<KInstruction *, int> >::const_reverse_iterator
           it = reverseInstructionList.rbegin(),
           ie = reverseInstructionList.rend();
       it != ie; ++it) {
    llvm::Instruction *i = (*it).first->inst;
    int flag = (*it).second;
    if (flag == 1) {
      // 1- call getCondition on the cond argument of the branch instruction
      // 2- create and expression from the condition and this->WPExpr

      ref<Expr> cond = TxExprHelper::simplifyNot(getBrCondition(i));
      if (True() == WPExpr) {
        WPExpr = cond;
      } else {
        WPExpr = AndExpr::create(WPExpr, cond);
      }

      //      llvm::outs() << "--- start 1 ---\n";
      //      i->dump();
      //      cond->dump();
      //      WPExpr->dump();
      //      llvm::outs() << "--- end 1 ---\n";

    } else if (flag == 2) {
      // 1- call getCondition on the cond argument of the branch instruction
      // 2- generate not(condition): expr::not(condition)
      // 3- create and expression from the condition and this->WPExpr
      ref<Expr> negCond =
          TxExprHelper::simplifyNot(NotExpr::create(getBrCondition(i)));
      if (True() == WPExpr) {
        WPExpr = negCond;
      } else {
        WPExpr = AndExpr::create(WPExpr, negCond);
      }

      //      llvm::outs() << "--- start 2 ---\n";
      //      i->dump();
      //      getBrCondition(i)->dump();
      //      negCond->dump();
      //      WPExpr->dump();
      //      llvm::outs() << "--- end 2 ---\n";
    } else if (i->getOpcode() == llvm::Instruction::Store) {
      //                  llvm::outs() << "--- start 3 ---\n";
      //                  WPExpr->dump();
      WPExpr = getPrevExpr(WPExpr, i);

      //                  i->dump();
      //                  WPExpr->dump();
      //                  llvm::outs() << "--- end 3 ---\n";
    }
  }
  //  llvm::outs() << "--- start simplifyLinear ---\n";
  //  WPExpr->dump();

  //  WPExpr = TxExprHelper::simplifyLinear(WPExpr);
  //  WPExpr = TxExprHelper::rangSimplify(WPExpr);
  //  WPExpr->dump();
  //  llvm::outs() << "--- end simplifyLinear ---\n";

  return WPExpr;
}

ref<Expr> TxWeakestPreCondition::getPrevExpr(ref<Expr> e,
                                             llvm::Instruction *i) {
  ref<Expr> ret = e;

  //  llvm::outs() << "\n***Start TxWeakestPreCondition::getPrevExpr***\n";
  //  i->dump();
  //  llvm::outs() << "\n***End TxWeakestPreCondition::getPrevExpr***\n";

  switch (i->getOpcode()) {
  case llvm::Instruction::Store: {
    if (!TxWPHelper::isTargetDependent(wpStore, i->getOperand(1), e)) {
      break;
    }
    ref<Expr> left = this->generateExprFromOperand(i, 0);
    ref<Expr> right = this->generateExprFromOperand(i, 1);
    ref<Expr> eqExpr = EqExpr::create(right, left);

    //        llvm::outs() << "--- Begin substitution ---\n";
    //        //    llvm::outs() << "[i]----\n";
    //        //    i->dump();
    //        llvm::outs() << "[e]----\n";
    //        e->dump();
    //        llvm::outs() << "[left]----\n";
    //        left->dump();
    //        llvm::outs() << "[right]----\n";
    //        right->dump();

    ref<Expr> result = TxWPHelper::substituteExpr(e, right, left);

    //            llvm::outs() << "[result]----\n";
    //            result->dump();
    //            llvm::outs() << "--- End substitution ---\n";

    ret = result;
    break;
  }

  default: {
    //    klee_message("+++++++++++++++++++++++++++++++++++++++++++++");
    //    klee_message("Instruction ignored: ");
    //    i->dump();
    //    klee_message("+++++++++++++++++++++++++++++++++++++++++++++");
  }
  }
  return ret;
}

ref<Expr> TxWeakestPreCondition::getBrCondition(llvm::Instruction *ins) {
  if (!llvm::isa<llvm::BranchInst>(ins)) {
    klee_error(
        "TxWeakestPreCondition::getBrCondition: not a Branch instruction!");
    return True();
  }
  llvm::BranchInst *br = llvm::dyn_cast<llvm::BranchInst>(ins);
  return getCondition(br->getCondition());
}

ref<Expr> TxWeakestPreCondition::getCondition(llvm::Value *value) {
  ref<Expr> result;
  if (llvm::isa<llvm::CmpInst>(value)) {
    llvm::CmpInst *cmp = dyn_cast<llvm::CmpInst>(value);
    result = getCmpCondition(cmp);
  } else if (llvm::isa<llvm::BinaryOperator>(value)) {
    llvm::Instruction *binOp = dyn_cast<llvm::Instruction>(value);
    ref<Expr> left = this->generateExprFromOperand(binOp, 0);
    ref<Expr> right = this->generateExprFromOperand(binOp, 1);
    switch (binOp->getOpcode()) {
    case llvm::Instruction::And: {
      result = AndExpr::create(left, right);
      break;
    }
    case llvm::Instruction::Or: {
      result = OrExpr::create(left, right);
      break;
    }
    default:
      klee_error("TxWeakestPreCondition::getCondition: Binary operator is not "
                 "implemented yet!");
    }
  } else {
    klee_error("TxWeakestPreCondition::getCondition: Binary operator is not "
               "implemented yet!");
  }
  return result;
}

ref<Expr> TxWeakestPreCondition::getCmpCondition(llvm::CmpInst *cmp) {
  // Getting the expressions from the left and right operand

  ref<Expr> left = this->generateExprFromOperand(cmp, 0);
  ref<Expr> right = this->generateExprFromOperand(cmp, 1);
  ref<Expr> result;
  // second step is to Storing the updated WP expression
  switch (cmp->getPredicate()) {
  case llvm::CmpInst::ICMP_EQ:
    result = EqExpr::create(left, right);
    break;
  case llvm::CmpInst::ICMP_NE:
    result = NeExpr::create(left, right);
    break;
  case llvm::CmpInst::ICMP_UGT:
    result = UgtExpr::create(left, right);
    break;
  case llvm::CmpInst::ICMP_UGE:
    result = UgeExpr::create(left, right);
    break;
  case llvm::CmpInst::ICMP_ULT:
    result = UltExpr::create(left, right);
    break;
  case llvm::CmpInst::ICMP_ULE:
    result = UleExpr::create(left, right);
    break;
  case llvm::CmpInst::ICMP_SGT:
    result = SgtExpr::create(left, right);
    break;
  case llvm::CmpInst::ICMP_SGE:
    result = SgeExpr::create(left, right);
    break;
  case llvm::CmpInst::ICMP_SLT:
    result = SltExpr::create(left, right);
    break;
  case llvm::CmpInst::ICMP_SLE:
    result = SleExpr::create(left, right);
    break;
  // todo Handle Floating Point
  case llvm::CmpInst::FCMP_FALSE:
    klee_error("FCMP_FALSE not implemented yet!");
    break;
  case llvm::CmpInst::FCMP_OEQ:
    klee_error("FCMP_OEQ not implemented yet!");
    break;
  case llvm::CmpInst::FCMP_OGT:
    klee_error("FCMP_OGT not implemented yet!");
    break;
  case llvm::CmpInst::FCMP_OGE:
    klee_error("FCMP_OGE not implemented yet!");
    break;
  case llvm::CmpInst::FCMP_OLT:
    klee_error("FCMP_OLT not implemented yet!");
    break;
  case llvm::CmpInst::FCMP_OLE:
    klee_error("FCMP_OLE not implemented yet!");
    break;
  case llvm::CmpInst::FCMP_ONE:
    klee_error("FCMP_ONE not implemented yet!");
    break;
  case llvm::CmpInst::FCMP_ORD:
    klee_error("FCMP_ORD not implemented yet!");
    break;
  case llvm::CmpInst::FCMP_UNO:
    klee_error("FCMP_UNO not implemented yet!");
    break;
  case llvm::CmpInst::FCMP_UEQ:
    klee_error("FCMP_UEQ not implemented yet!");
    break;
  case llvm::CmpInst::FCMP_UGT:
    klee_error("FCMP_UGT not implemented yet!");
    break;
  case llvm::CmpInst::FCMP_UGE:
    klee_error("FCMP_UGE not implemented yet!");
    break;
  case llvm::CmpInst::FCMP_ULT:
    klee_error("FCMP_ULT not implemented yet!");
    break;
  case llvm::CmpInst::FCMP_ULE:
    klee_error("FCMP_ULE not implemented yet!");
    break;
  case llvm::CmpInst::FCMP_UNE:
    klee_error("FCMP_UNE not implemented yet!");
    break;
  case llvm::CmpInst::FCMP_TRUE:
    klee_error("FCMP_TRUE not implemented yet!");
    break;
  case llvm::CmpInst::BAD_FCMP_PREDICATE:
    klee_error("BAD_FCMP_PREDICATE not implemented yet!");
    break;
  case llvm::CmpInst::BAD_ICMP_PREDICATE:
    klee_error("BAD_ICMP_PREDICATE not implemented yet!");
    break;
  }
  return result;
}

ref<Expr> TxWeakestPreCondition::generateExprFromOperand(llvm::Instruction *i,
                                                         int operand,
                                                         ref<Expr> offset) {
  //  llvm::outs()
  //      << "\n***Start TxWeakestPreCondition::generateExprFromOperand***\n";
  //  i->dump();
  //  llvm::outs()
  //      << "\n***End TxWeakestPreCondition::generateExprFromOperand***\n";

  // Generating WP from Operand1
  ref<Expr> ret;
  llvm::Value *val = i->getOperand(operand);
  if (isa<llvm::ConstantInt>(val)) {
    llvm::ConstantInt *CI = dyn_cast<llvm::ConstantInt>(val);
    if (CI->getBitWidth() <= 8)
      ret = ConstantExpr::create(CI->getZExtValue(), Expr::Int8);
    else if (CI->getBitWidth() <= 16)
      ret = ConstantExpr::create(CI->getZExtValue(), Expr::Int16);
    else if (CI->getBitWidth() <= 32)
      ret = ConstantExpr::create(CI->getZExtValue(), Expr::Int32);
    else
      ret = ConstantExpr::create(CI->getZExtValue(), Expr::Int64);
  } else if (isa<llvm::LoadInst>(val)) {
    llvm::LoadInst *inst = dyn_cast<llvm::LoadInst>(val);
    if (isa<llvm::GlobalValue>(inst->getOperand(0))) {
      ret = dependency->getAddress(inst->getOperand(0), &(wpStore->ac),
                                   wpStore->array, this, offset);

    } else if (isa<llvm::ConstantExpr>(inst->getOperand(0))) {
      llvm::ConstantExpr *gep =
          dyn_cast<llvm::ConstantExpr>(inst->getOperand(0));
      inst->dump();
      klee_error("Constant GEP not handled yet!");
      ret = dependency->getPointerAddress(gep, &(wpStore->ac), wpStore->array,
                                          this);
    } else if (isa<llvm::LoadInst>(inst->getOperand(0))) {
      llvm::LoadInst *inst2 = dyn_cast<llvm::LoadInst>(inst->getOperand(0));
      ret = dependency->getAddress(inst2->getOperand(0), &(wpStore->ac),
                                   wpStore->array, this, offset);
    } else if (isa<llvm::GetElementPtrInst>(inst->getOperand(0))) {
      llvm::GetElementPtrInst *gep =
          dyn_cast<llvm::GetElementPtrInst>(inst->getOperand(0));

      // Offset
      ref<Expr> offset = this->generateExprFromOperand(gep, 2);
      ret = this->generateExprFromOperand(gep, 0, offset);

    } else {
      ret = dependency->getAddress(inst->getOperand(0), &(wpStore->ac),
                                   wpStore->array, this, offset);
    }
  } else if (isa<llvm::BinaryOperator>(val)) {
    llvm::Instruction *op1 = dyn_cast<llvm::Instruction>(val);
    ref<Expr> arg1 = generateExprFromOperand(op1, 0);
    ref<Expr> arg2 = generateExprFromOperand(op1, 1);

    switch (op1->getOpcode()) {
    case llvm::Instruction::Add: {
      ret = AddExpr::create(arg1, arg2);
      break;
    }
    case llvm::Instruction::Sub: {
      ret = SubExpr::create(arg1, arg2);
      break;
    }
    case llvm::Instruction::Mul: {
      ret = MulExpr::create(arg1, arg2);
      break;
    }
    case llvm::Instruction::UDiv: {
      ret = UDivExpr::create(arg1, arg2);
      break;
    }
    case llvm::Instruction::SDiv: {
      ret = SDivExpr::create(arg1, arg2);
      break;
    }
    case llvm::Instruction::URem: {
      ret = URemExpr::create(arg1, arg2);
      break;
    }
    case llvm::Instruction::SRem: {
      ret = SRemExpr::create(arg1, arg2);
      break;
    }
    case llvm::Instruction::And: {
      ret = AndExpr::create(arg1, arg2);
      break;
    }
    case llvm::Instruction::Or: {
      ret = OrExpr::create(arg1, arg2);
      break;
    }
    case llvm::Instruction::Xor: {
      ret = XorExpr::create(arg1, arg2);
      break;
    }
    case llvm::Instruction::Shl: {
      ret = ShlExpr::create(arg1, arg2);
      break;
    }
    case llvm::Instruction::LShr: {
      ret = LShrExpr::create(arg1, arg2);
      break;
    }
    case llvm::Instruction::AShr: {
      ret = AShrExpr::create(arg1, arg2);
      break;
    }
    default: {
      klee_error(
          "TxWeakestPreCondition::generateExprFromOperand Binary Operand "
          "not implemented...\n");
    }
    }
  } else if (isa<llvm::CastInst>(val)) {
    llvm::CastInst *op1 = dyn_cast<llvm::CastInst>(val);
    ref<Expr> arg1 = generateExprFromOperand(op1, 0);

    Expr::Width width = Expr::InvalidWidth;
    if (op1->getDestTy()->isEmptyTy())
      width = Expr::InvalidWidth;
    else if (op1->getDestTy()->isIntegerTy(1))
      width = Expr::Bool;
    else if (op1->getDestTy()->isIntegerTy(8))
      width = Expr::Int8;
    else if (op1->getDestTy()->isHalfTy())
      width = Expr::Int16;
    else if (op1->getDestTy()->isIntegerTy())
      width = Expr::Int32;
    else if (op1->getDestTy()->isDoubleTy())
      width = Expr::Int64;
    else if (op1->getDestTy()->isFloatTy())
      width = Expr::Fl80;

    switch (op1->getOpcode()) {
    case llvm::Instruction::SExt: {
      ret = SExtExpr::create(arg1, width);
      break;
    }

    case llvm::Instruction::ZExt: {
      ret = ZExtExpr::create(arg1, width);
      break;
    }
    case llvm::Instruction::AddrSpaceCast:
    case llvm::Instruction::BitCast:
    case llvm::Instruction::FPExt:
    case llvm::Instruction::FPToSI:
    case llvm::Instruction::FPToUI:
    case llvm::Instruction::FPTrunc:
    case llvm::Instruction::IntToPtr:
    case llvm::Instruction::PtrToInt:
    case llvm::Instruction::SIToFP:
    case llvm::Instruction::Trunc:
    case llvm::Instruction::UIToFP:
    default: {
      klee_error("TxWeakestPreCondition::generateExprFromOperand Unary Operand "
                 "not implemented...\n");
    }
    }
  } else if (isa<llvm::AllocaInst>(val)) {
    ret = dependency->getAddress(val, &(wpStore->ac), wpStore->array, this,
                                 offset);
  } else if (llvm::isa<llvm::CmpInst>(val)) {
    llvm::CmpInst *cmp = dyn_cast<llvm::CmpInst>(val);
    ret = getCmpCondition(cmp);
  } else if (llvm::isa<llvm::GlobalVariable>(val)) {
    ret = dependency->getAddress(val, &(wpStore->ac), wpStore->array, this,
                                 offset);
  } else if (llvm::isa<llvm::Argument>(val)) {
    klee_error("llvm::isa<llvm::Argument>(operand1)");

    // TODO: Argument is correct?
    //    llvm::Argument arg = dyn_cast<llvm::Argument>(operand1);
    ret = dependency->getAddress(val, &(wpStore->ac), wpStore->array, this,
                                 offset);
  } else if (llvm::isa<llvm::PHINode>(val)) {
    llvm::PHINode *phi = dyn_cast<llvm::PHINode>(val);
    llvm::Instruction *prevInst = node->getPreviousInstruction(phi);
    llvm::BasicBlock *prevInstBB = prevInst->getParent();
    int phiFlag = false;
    for (int i = 0; i < phi->getNumIncomingValues(); i++) {
      if (phi->getIncomingBlock(i) == prevInstBB) {
        llvm::Value *prevValue = phi->getIncomingValue(i);
        ret = dependency->getAddress(prevValue, &(wpStore->ac), wpStore->array,
                                     this, offset);
        phiFlag = true;
      }
    }
    if (!phiFlag)
      klee_error("TxWeakestPreCondition::generateExprFromOperand Phi "
                 "instruction is not matching any incoming values!");
  } else if (isa<llvm::GetElementPtrInst>(val)) {
    llvm::GetElementPtrInst *gep = dyn_cast<llvm::GetElementPtrInst>(val);

    // Offset
    ref<Expr> newOffset = this->generateExprFromOperand(gep, 2);
    ref<Expr> arraySize = ConstantExpr::create(gep->getPointerOperandType()
                                                   ->getArrayElementType()
                                                   ->getArrayNumElements(),
                                               Expr::Int32);
    if (!offset.isNull())
      newOffset =
          AddExpr::create(MulExpr::create(newOffset, arraySize), offset);
    ret = this->generateExprFromOperand(gep, 0, newOffset);

  } else {
    llvm::errs() << "Value:";
    val->dump();
    llvm::errs() << "\nType:";
    val->getType()->dump();
    klee_error("TxWeakestPreCondition::generateExprFromOperand Remaining"
               " cases not implemented yet\n");
  }
  return ret;
}
