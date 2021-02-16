//===-- TxTree.cpp - Interpolation tree -------------------------*- C++ -*-===//
//
//               The Tracer-X KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// This file contains the implementations of the classes for
/// interpolation and subsumption checks for search-space reduction.
///
//===----------------------------------------------------------------------===//

#include "TxTree.h"

#include "TimingSolver.h"

#include "TxDependency.h"
#include "TxShadowArray.h"
#include "Memory.h"
#include <fstream>
#include <klee/CommandLine.h>
#include <klee/Expr.h>
#include <klee/Internal/Support/ErrorHandling.h>
#include <klee/Solver.h>
#include <klee/SolverStats.h>
#include <klee/util/ExprPPrinter.h>
#include <klee/util/TxExprUtil.h>
#include <klee/util/TxPrintUtil.h>
#include <vector>

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 5)
#include <llvm/IR/DebugInfo.h>
#elif LLVM_VERSION_CODE >= LLVM_VERSION(3, 2)
#include <llvm/DebugInfo.h>
#else
#include <llvm/Analysis/DebugInfo.h>
#endif

using namespace klee;

Statistic TxSubsumptionTableEntry::concretelyAddressedStoreExpressionBuildTime(
    "concretelyAddressedStoreExpressionBuildTime", "concreteStoreTime");
Statistic
TxSubsumptionTableEntry::symbolicallyAddressedStoreExpressionBuildTime(
    "symbolicallyAddressedStoreExpressionBuildTime", "symbolicStoreTime");
Statistic TxSubsumptionTableEntry::solverAccessTime("solverAccessTime",
                                                    "solverAccessTime");

TxSubsumptionTableEntry::TxSubsumptionTableEntry(
    TxTreeNode *node, const std::vector<llvm::Instruction *> &callHistory)
    : programPoint(node->getProgramPoint()),
      nodeSequenceNumber(node->getNodeSequenceNumber()) {
  std::map<ref<Expr>, ref<Expr> > substitution;
  existentials.clear();
  interpolant = node->getInterpolant(existentials, substitution);
  prevProgramPoint = node->getPrevProgramPoint();
  phiValues = node->getPhiValue();

  node->getStoredCoreExpressions(
      callHistory, substitution, existentials, concretelyAddressedStore,
      symbolicallyAddressedStore, concretelyAddressedHistoricalStore,
      symbolicallyAddressedHistoricalStore);

  if (MarkGlobal) {
    markedGlobal = node->getDependency()->getMarkedGlobal();
  }

  if (WPInterpolant)
    wpInterpolant = node->generateWPInterpolant();
}

TxSubsumptionTableEntry::~TxSubsumptionTableEntry() {}

ref<Expr> TxSubsumptionTableEntry::makeConstraint(
    ExecutionState &state, ref<TxInterpolantValue> tabledValue,
    ref<TxInterpolantValue> stateValue, ref<Expr> tabledOffset,
    ref<Expr> stateOffset, std::set<ref<TxStateValue> > &coreValues,
    std::map<ref<TxStateValue>, std::set<uint64_t> > &corePointerValues,
    std::map<ref<TxAllocationInfo>, ref<TxAllocationInfo> > &unifiedBases,
    int debugSubsumptionLevel) const {
  ref<Expr> constraint;

#ifdef ENABLE_Z3
  if (tabledValue->getExpression()->getWidth() !=
      stateValue->getExpression()->getWidth()) {
    // We conservatively require that the addresses should not be
    // equal whenever their values are of different width
    constraint = EqExpr::create(ConstantExpr::create(0, Expr::Bool),
                                EqExpr::create(tabledOffset, stateOffset));
  } else if (TxDependency::boundInterpolation() && tabledValue->isPointer() &&
             stateValue->isPointer()) {
    if (!ExactAddressInterpolant && tabledValue->useBound()) {
      std::set<uint64_t> bounds;
      ref<Expr> boundsCheck = tabledValue->getBoundsCheck(
          stateValue, bounds, unifiedBases, debugSubsumptionLevel);

      if (!boundsCheck.isNull()) {
        if (!boundsCheck->isTrue()) {
          if (!boundsCheck->isFalse()) {
            // Implication: if tabled (interpolant)'s address == state address
            // then bounds check must hold
            constraint =
                EqExpr::create(ConstantExpr::create(0, Expr::Bool),
                               EqExpr::create(tabledOffset, stateOffset));
            constraint = OrExpr::create(constraint, boundsCheck);
          } else {
            if (debugSubsumptionLevel >= 1) {
              std::string msg;
              klee_message("#%lu=>#%lu: Check failure due to failure in "
                           "memory bounds check%s",
                           state.txTreeNode->getNodeSequenceNumber(),
                           nodeSequenceNumber, msg.c_str());
            }

            assert(constraint.isNull() && "must return a null constraint");
            return constraint;
          }
        }

        // We record the LLVM value of the pointer
        corePointerValues[stateValue->getOriginalValue()] = bounds;
        return constraint;
      }
    }

    ref<Expr> offsetsCheck = tabledValue->getOffsetsCheck(
        stateValue, unifiedBases, debugSubsumptionLevel);
    if (offsetsCheck->isFalse()) {
      if (debugSubsumptionLevel >= 1) {
        klee_message("#%lu=>#%lu: Check failure due to failure in "
                     "offset equality check",
                     state.txTreeNode->getNodeSequenceNumber(),
                     nodeSequenceNumber);
      }
      return constraint;
    }
    constraint = offsetsCheck;
  } else {
    // Implication: if tabledConcreteAddress == stateSymbolicAddress, then
    // tabledValue->getExpression() == stateValue->getExpression()
    constraint = OrExpr::create(
        EqExpr::create(ConstantExpr::create(0, Expr::Bool),
                       EqExpr::create(tabledOffset, stateOffset)),
        EqExpr::create(tabledValue->getExpression(),
                       stateValue->getExpression()));
  }

  // We record the value of the pointer for interpolation marking
  coreValues.insert(stateValue->getOriginalValue());
#endif
  return constraint;
}

bool
TxSubsumptionTableEntry::hasVariableInSet(std::set<const Array *> &existentials,
                                          ref<Expr> expr) {
  for (int i = 0, numKids = expr->getNumKids(); i < numKids; ++i) {
    if (llvm::isa<ReadExpr>(expr)) {
      ReadExpr *readExpr = llvm::dyn_cast<ReadExpr>(expr);
      const Array *array = (readExpr->updates).root;
      for (std::set<const Array *>::const_iterator it = existentials.begin(),
                                                   ie = existentials.end();
           it != ie; ++it) {
        if ((*it) == array)
          return true;
      }
    } else if (hasVariableInSet(existentials, expr->getKid(i)))
      return true;
  }
  return false;
}

ref<Expr> TxSubsumptionTableEntry::getBoundFreeConjunction(
    std::set<const Array *> &existentials, ref<Expr> expr) {

  if (llvm::isa<AndExpr>(expr)) {
    ref<Expr> boundFree1 =
        getBoundFreeConjunction(existentials, expr->getKid(0));
    if (boundFree1.isNull())
      return boundFree1;
    ref<Expr> boundFree2 =
        getBoundFreeConjunction(existentials, expr->getKid(1));
    if (boundFree2.isNull())
      return boundFree2;
    return AndExpr::create(boundFree1, boundFree2);
  }

  if (hasVariableInSet(existentials, expr)) {
    if (hasVariableNotInSet(existentials, expr)) {
      ref<Expr> nullExpr;
      return nullExpr;
    }
    return ConstantExpr::create(1, Expr::Bool);
  }

  // expr has no existentials, may even have no variables
  return expr;
}

bool TxSubsumptionTableEntry::hasVariableNotInSet(
    std::set<const Array *> &existentials, ref<Expr> expr) {
  for (int i = 0, numKids = expr->getNumKids(); i < numKids; ++i) {
    if (llvm::isa<ReadExpr>(expr)) {
      ReadExpr *readExpr = llvm::dyn_cast<ReadExpr>(expr);
      const Array *array = (readExpr->updates).root;
      for (std::set<const Array *>::const_iterator it = existentials.begin(),
                                                   ie = existentials.end();
           it != ie; ++it) {
        if ((*it) == array)
          return false;
      }
      return true;
    } else if (hasVariableNotInSet(existentials, expr->getKid(i)))
      return true;
  }
  return false;
}

ref<Expr>
TxSubsumptionTableEntry::simplifyArithmeticBody(ref<Expr> existsExpr,
                                                bool &hasExistentialsOnly) {
  ExistsExpr *expr = llvm::dyn_cast<ExistsExpr>(existsExpr);

  assert(expr && "expression is not existentially quantified");

  // Assume the we shall return general ExistsExpr that does not contain
  // only existential variables.
  hasExistentialsOnly = false;

  // We assume that the body is always a conjunction of interpolant in terms of
  // shadow (existentially-quantified) variables and state equality constraints,
  // which may contain both normal and shadow variables.
  ref<Expr> body = expr->body;

  // If the post-simplified body was a constant, simply return the body;
  if (llvm::isa<ConstantExpr>(body))
    return body;

  // We only simplify a conjunction of interpolant and equalities
  if (!llvm::isa<AndExpr>(body)) {
    hasExistentialsOnly = !hasVariableNotInSet(expr->variables, body);
    return existsExpr;
  }

  // The equality constraint is only a single disjunctive clause
  // of a CNF formula. In this case we simplify nothing.
  if (llvm::isa<OrExpr>(body->getKid(1)))
    return existsExpr;

  // Here we process equality constraints of shadow and normal variables.
  // The following procedure returns simplified version of the expression
  // by reducing any equality expression into constant (TRUE/FALSE).
  // if body is A and (Eq 2 4), body can be simplified into false.
  // if body is A and (Eq 2 2), body can be simplified into A.
  //
  // Along the way, It also collects the remaining equalities in equalityPack.
  // The equality constraints (body->getKid(1)) is a CNF of the form
  // c1 /\ ... /\ cn. This procedure collects into equalityPack all ci for
  // 1<=i<=n which are atomic equalities, to be used in simplifying the
  // interpolant.
  std::vector<ref<Expr> > equalityPack;

  ref<Expr> fullEqualityConstraint =
      simplifyEqualityExpr(equalityPack, body->getKid(1));

  if (fullEqualityConstraint->isFalse())
    return fullEqualityConstraint;

  // Try to simplify the interpolant. If the resulting simplification
  // was the constant true, then the equality constraints would contain
  // equality with constants only and no equality with shadow (existential)
  // variables, hence it should be safe to simply return the equality
  // constraint.
  std::vector<ref<Expr> > interpolantPack;

  ref<Expr> simplifiedInterpolant =
      simplifyInterpolantExpr(interpolantPack, body->getKid(0));
  if (simplifiedInterpolant->isTrue())
    return fullEqualityConstraint;

  if (fullEqualityConstraint->isTrue()) {
    // This is the case when the result is still an existentially-quantified
    // formula, but one that does not contain free variables.
    hasExistentialsOnly =
        !hasVariableNotInSet(expr->variables, simplifiedInterpolant);
    if (hasExistentialsOnly) {
      return existsExpr->rebuild(&simplifiedInterpolant);
    }
  }

  ref<Expr> newInterpolant;

  // fullEqualityConstraint will necessarily be part of the return value of this
  // function, so we check for existentials in it before proceeding further.
  hasExistentialsOnly =
      !hasVariableNotInSet(expr->variables, fullEqualityConstraint);

  for (std::vector<ref<Expr> >::iterator it = interpolantPack.begin(),
                                         ie = interpolantPack.end();
       it != ie; ++it) {

    ref<Expr> interpolantAtom = (*it); // For example C cmp D

    // only process the interpolant that still has existential variables in
    // it.
    if (hasVariableInSet(expr->variables, interpolantAtom)) {
      for (std::vector<ref<Expr> >::iterator it1 = equalityPack.begin(),
                                             ie1 = equalityPack.end();
           it1 != ie1; ++it1) {

        ref<Expr> equalityConstraint =
            *it1; // For example, say this constraint is A == B
        if (equalityConstraint->isFalse()) {
          return ConstantExpr::create(0, Expr::Bool);
        } else if (equalityConstraint->isTrue()) {
          return ConstantExpr::create(1, Expr::Bool);
        }
        // Left-hand side of the equality formula (A in our example) that
        // contains
        // the shadow expression (we assume that the
        // existentially-quantified
        // shadow variable is always on the left side).
        ref<Expr> equalityConstraintLeft = equalityConstraint->getKid(0);

        // Right-hand side of the equality formula (B in our example) that
        // does
        // not contain existentially-quantified shadow variables.
        ref<Expr> equalityConstraintRight = equalityConstraint->getKid(1);

        ref<Expr> newIntpLeft;
        ref<Expr> newIntpRight;

        // When the if condition holds, we perform substitution
        if (interpolantAtom->getNumKids() > 0 &&
            !llvm::isa<ConstantExpr>(equalityConstraintLeft) &&
            hasSubExpression(equalityConstraintLeft,
                             interpolantAtom->getKid(0))) {
          // Here we perform substitution, where given
          // an interpolant atom and an equality constraint,
          // we try to find a subexpression in the equality constraint
          // that matches the lhs expression of the interpolant atom.

          // Here we assume that the equality constraint is A == B and the
          // interpolant atom is C cmp D.

          // newIntpLeft == B
          newIntpLeft = equalityConstraintRight;

          // If equalityConstraintLeft does not have any arithmetic
          // operation
          // we could directly assign newIntpRight = D, otherwise,
          // newIntpRight == A[D/C]
          if (!llvm::isa<BinaryExpr>(equalityConstraintLeft) ||
              equalityConstraintLeft->getWidth() !=
                  interpolantAtom->getKid(1)->getWidth())
            newIntpRight = interpolantAtom->getKid(1);
          else {
            // newIntpRight is A, but with every occurrence of C replaced
            // with D
            // i.e., newIntpRight == A[D/C]
            newIntpRight =
                replaceExpr(equalityConstraintLeft, interpolantAtom->getKid(0),
                            interpolantAtom->getKid(1));
          }

          interpolantAtom = TxShadowArray::createBinaryOfSameKind(
              interpolantAtom, newIntpLeft, newIntpRight);
        }
      }
    }

    // We add the modified interpolant conjunct into a conjunction of
    // new interpolants.
    if (!newInterpolant.isNull()) {
      newInterpolant = AndExpr::create(newInterpolant, interpolantAtom);
    } else {
      newInterpolant = interpolantAtom;
    }

    hasExistentialsOnly =
        (hasExistentialsOnly &&
         !hasVariableNotInSet(expr->variables, interpolantAtom));
  }

  ref<Expr> newBody;

  if (!newInterpolant.isNull()) {
    if (!hasVariableInSet(expr->variables, newInterpolant))
      return newInterpolant;

    newBody = AndExpr::create(newInterpolant, fullEqualityConstraint);
  } else {
    hasExistentialsOnly =
        (hasExistentialsOnly &&
         !hasVariableNotInSet(expr->variables, simplifiedInterpolant));
    newBody = AndExpr::create(simplifiedInterpolant, fullEqualityConstraint);
  }

  return existsExpr->rebuild(&newBody);
}

ref<Expr> TxSubsumptionTableEntry::replaceExpr(ref<Expr> originalExpr,
                                               ref<Expr> replacedExpr,
                                               ref<Expr> replacementExpr) {
  // We only handle binary expressions
  if (!llvm::isa<BinaryExpr>(originalExpr) ||
      llvm::isa<ConcatExpr>(originalExpr))
    return originalExpr;

  if (originalExpr->getKid(0) == replacedExpr)
    return TxShadowArray::createBinaryOfSameKind(originalExpr, replacementExpr,
                                                 originalExpr->getKid(1));

  if (originalExpr->getKid(1) == replacedExpr)
    return TxShadowArray::createBinaryOfSameKind(
        originalExpr, originalExpr->getKid(0), replacementExpr);

  return TxShadowArray::createBinaryOfSameKind(
      originalExpr,
      replaceExpr(originalExpr->getKid(0), replacedExpr, replacementExpr),
      replaceExpr(originalExpr->getKid(1), replacedExpr, replacementExpr));
}

bool TxSubsumptionTableEntry::hasSubExpression(ref<Expr> expr,
                                               ref<Expr> subExpr) {
  if (expr == subExpr)
    return true;
  if (expr->getNumKids() < 2 && expr != subExpr)
    return false;

  return hasSubExpression(expr->getKid(0), subExpr) ||
         hasSubExpression(expr->getKid(1), subExpr);
}

ref<Expr> TxSubsumptionTableEntry::simplifyInterpolantExpr(
    std::vector<ref<Expr> > &interpolantPack, ref<Expr> expr) {
  if (expr->getNumKids() < 2)
    return expr;

  if (llvm::isa<EqExpr>(expr) && llvm::isa<ConstantExpr>(expr->getKid(0)) &&
      llvm::isa<ConstantExpr>(expr->getKid(1))) {
    return (expr->getKid(0) == expr->getKid(1))
               ? ConstantExpr::create(1, Expr::Bool)
               : ConstantExpr::create(0, Expr::Bool);
  } else if (llvm::isa<NeExpr>(expr) &&
             llvm::isa<ConstantExpr>(expr->getKid(0)) &&
             llvm::isa<ConstantExpr>(expr->getKid(1))) {
    return (expr->getKid(0) != expr->getKid(1))
               ? ConstantExpr::create(1, Expr::Bool)
               : ConstantExpr::create(0, Expr::Bool);
  }

  ref<Expr> lhs = expr->getKid(0);
  ref<Expr> rhs = expr->getKid(1);

  if (!llvm::isa<AndExpr>(expr)) {

    // If the current expression has a form like (Eq false P), where P is some
    // comparison, we change it into the negation of P.
    if (llvm::isa<EqExpr>(expr) && expr->getKid(0)->getWidth() == Expr::Bool &&
        expr->getKid(0)->isFalse()) {
      if (llvm::isa<SltExpr>(rhs)) {
        expr = SgeExpr::create(rhs->getKid(0), rhs->getKid(1));
      } else if (llvm::isa<SgeExpr>(rhs)) {
        expr = SltExpr::create(rhs->getKid(0), rhs->getKid(1));
      } else if (llvm::isa<SleExpr>(rhs)) {
        expr = SgtExpr::create(rhs->getKid(0), rhs->getKid(1));
      } else if (llvm::isa<SgtExpr>(rhs)) {
        expr = SleExpr::create(rhs->getKid(0), rhs->getKid(1));
      }
    }

    // Collect unique interpolant expressions in one vector
    if (std::find(interpolantPack.begin(), interpolantPack.end(), expr) ==
        interpolantPack.end())
      interpolantPack.push_back(expr);

    return expr;
  }

  ref<Expr> simplifiedLhs = simplifyInterpolantExpr(interpolantPack, lhs);
  if (simplifiedLhs->isFalse())
    return simplifiedLhs;

  ref<Expr> simplifiedRhs = simplifyInterpolantExpr(interpolantPack, rhs);
  if (simplifiedRhs->isFalse())
    return simplifiedRhs;

  if (simplifiedLhs->isTrue())
    return simplifiedRhs;

  if (simplifiedRhs->isTrue())
    return simplifiedLhs;

  return AndExpr::create(simplifiedLhs, simplifiedRhs);
}

ref<Expr> TxSubsumptionTableEntry::simplifyEqualityExpr(
    std::vector<ref<Expr> > &equalityPack, ref<Expr> expr) {
  if (expr->getNumKids() < 2)
    return expr;

  if (llvm::isa<EqExpr>(expr)) {
    if (llvm::isa<ConstantExpr>(expr->getKid(0)) &&
        llvm::isa<ConstantExpr>(expr->getKid(1))) {
      return (expr->getKid(0) == expr->getKid(1))
                 ? ConstantExpr::create(1, Expr::Bool)
                 : ConstantExpr::create(0, Expr::Bool);
    }

    // Collect unique equality and in-equality expressions in one vector
    if (std::find(equalityPack.begin(), equalityPack.end(), expr) ==
        equalityPack.end())
      equalityPack.push_back(expr);

    return expr;
  }

  if (llvm::isa<AndExpr>(expr)) {
    ref<Expr> lhs = simplifyEqualityExpr(equalityPack, expr->getKid(0));
    if (lhs->isFalse())
      return lhs;

    ref<Expr> rhs = simplifyEqualityExpr(equalityPack, expr->getKid(1));
    if (rhs->isFalse())
      return rhs;

    if (lhs->isTrue())
      return rhs;

    if (rhs->isTrue())
      return lhs;

    return AndExpr::create(lhs, rhs);
  } else if (llvm::isa<OrExpr>(expr)) {
    // We provide throw-away dummy equalityPack, as we do not use the atomic
    // equalities within disjunctive clause to simplify the interpolant.
    std::vector<ref<Expr> > dummy;
    ref<Expr> lhs = simplifyEqualityExpr(dummy, expr->getKid(0));
    if (lhs->isTrue())
      return lhs;

    ref<Expr> rhs = simplifyEqualityExpr(dummy, expr->getKid(1));
    if (rhs->isTrue())
      return rhs;

    if (lhs->isFalse())
      return rhs;

    if (rhs->isFalse())
      return lhs;

    return OrExpr::create(lhs, rhs);
  }

  if (expr->getWidth() == Expr::Bool)
    return expr;

  assert(!"Invalid expression type.");
}

void
TxSubsumptionTableEntry::getSubstitution(std::set<const Array *> &existentials,
                                         ref<Expr> equalities,
                                         std::map<ref<Expr>, ref<Expr> > &map) {
  // It is assumed the rhs is an expression on the free variables.
  if (llvm::isa<EqExpr>(equalities)) {
    ref<Expr> lhs = equalities->getKid(0);
    if (isVariable(lhs) && hasVariableInSet(existentials, lhs)) {
      map[lhs] = equalities->getKid(1);
    } else if (SExtExpr *lhsSExt = llvm::dyn_cast<SExtExpr>(lhs)) {
      // Here we skin a sign-extend expression to retrieve the variable within
      if (SExtExpr *rhsSExt = llvm::dyn_cast<SExtExpr>(equalities->getKid(1))) {
        if (lhsSExt->getWidth() == rhsSExt->getWidth()) {
          lhs = lhsSExt->getKid(0);
          if (isVariable(lhs) && hasVariableInSet(existentials, lhs)) {
            map[lhs] = rhsSExt->getKid(0);
          }
        }
      }
    } else if (ZExtExpr *lhsZExt = llvm::dyn_cast<ZExtExpr>(lhs)) {
      // Here we skin a zero-extend expression to retrieve the variable within
      if (ZExtExpr *rhsZExt = llvm::dyn_cast<ZExtExpr>(equalities->getKid(1))) {
        if (lhsZExt->getWidth() == rhsZExt->getWidth()) {
          lhs = lhsZExt->getKid(0);
          if (isVariable(lhs) && hasVariableInSet(existentials, lhs)) {
            map[lhs] = rhsZExt->getKid(0);
          }
        }
      }
    }
  } else if (llvm::isa<AndExpr>(equalities)) {
    getSubstitution(existentials, equalities->getKid(0), map);
    getSubstitution(existentials, equalities->getKid(1), map);
  }
}

ref<Expr>
TxSubsumptionTableEntry::removeUnsubstituted(std::set<const Array *> &variables,
                                             ref<Expr> equalities) {
  // It is assumed the lhs is an expression on the existentially-quantified
  // variable whereas the rhs is an expression on the free variables.
  if (llvm::isa<EqExpr>(equalities)) {
    ref<Expr> lhs = equalities->getKid(0);
    if (isVariable(lhs) && hasVariableInSet(variables, lhs)) {
      return ConstantExpr::create(1, Expr::Bool);
    } else if (SExtExpr *lhsSExt = llvm::dyn_cast<SExtExpr>(lhs)) {
      // Here we skin a sign-extend expression to retrieve the variable within
      if (SExtExpr *rhsSExt = llvm::dyn_cast<SExtExpr>(equalities->getKid(1))) {
        if (lhsSExt->getWidth() == rhsSExt->getWidth()) {
          lhs = lhsSExt->getKid(0);
          if (isVariable(lhs) && hasVariableInSet(variables, lhs)) {
            return ConstantExpr::create(1, Expr::Bool);
          }
        }
      }
    } else if (ZExtExpr *lhsZExt = llvm::dyn_cast<ZExtExpr>(lhs)) {
      // Here we skin a zero-extend expression to retrieve the variable within
      if (ZExtExpr *rhsZExt = llvm::dyn_cast<ZExtExpr>(equalities->getKid(1))) {
        if (lhsZExt->getWidth() == rhsZExt->getWidth()) {
          lhs = lhsZExt->getKid(0);
          if (isVariable(lhs) && hasVariableInSet(variables, lhs)) {
            return ConstantExpr::create(1, Expr::Bool);
          }
        }
      }
    }
    return equalities;
  }

  if (llvm::isa<AndExpr>(equalities)) {
    ref<Expr> lhs = removeUnsubstituted(variables, equalities->getKid(0));
    ref<Expr> rhs = removeUnsubstituted(variables, equalities->getKid(1));
    if (lhs->isTrue()) {
      if (rhs->isTrue()) {
        return ConstantExpr::create(1, Expr::Bool);
      }
      return rhs;
    } else {
      if (rhs->isTrue()) {
        return lhs;
      }
      return AndExpr::create(lhs, rhs);
    }
  }
  return equalities;
}

bool TxSubsumptionTableEntry::detectConflictPrimitives(ExecutionState &state,
                                                       ref<Expr> expr) {
  if (llvm::isa<ExistsExpr>(expr))
    return true;

  std::vector<ref<Expr> > conjunction;
  if (!fetchExprEqualityConjucts(conjunction, expr)) {
    return false;
  }

  for (std::vector<ref<Expr> >::const_iterator it1 = state.constraints.begin(),
                                               ie1 = state.constraints.end();
       it1 != ie1; ++it1) {

    if ((*it1)->getKind() != Expr::Eq)
      continue;

    for (std::vector<ref<Expr> >::const_iterator it2 = conjunction.begin(),
                                                 ie2 = conjunction.end();
         it2 != ie2; ++it2) {

      ref<Expr> stateConstraintExpr = it1->get();
      ref<Expr> exprEqConstraint = it2->get();

      if (stateConstraintExpr != exprEqConstraint &&
          (llvm::isa<EqExpr>(stateConstraintExpr) ||
           llvm::isa<EqExpr>(exprEqConstraint))) {

        if (stateConstraintExpr ==
                EqExpr::create(ConstantExpr::create(0, Expr::Bool),
                               exprEqConstraint) ||
            EqExpr::create(ConstantExpr::create(0, Expr::Bool),
                           stateConstraintExpr) == exprEqConstraint) {
          return false;
        }
      }
    }
  }

  return true;
}

bool TxSubsumptionTableEntry::fetchExprEqualityConjucts(
    std::vector<ref<Expr> > &conjunction, ref<Expr> expr) {

  if (!llvm::isa<AndExpr>(expr)) {
    if (expr->getKind() == Expr::Eq) {

      EqExpr *equality = llvm::dyn_cast<EqExpr>(expr);

      if (llvm::isa<ConstantExpr>(equality->getKid(0)) &&
          llvm::isa<ConstantExpr>(equality->getKid(1)) &&
          equality->getKid(0) != equality->getKid(1)) {
        return false;
      } else {
        conjunction.push_back(expr);
      }
    }
    return true;
  }

  return fetchExprEqualityConjucts(conjunction, expr->getKid(0)) &&
         fetchExprEqualityConjucts(conjunction, expr->getKid(1));
}

ref<Expr>
TxSubsumptionTableEntry::simplifyExistsExpr(ref<Expr> existsExpr,
                                            bool &hasExistentialsOnly) {
  assert(llvm::isa<ExistsExpr>(existsExpr));

  ExistsExpr *expr = llvm::dyn_cast<ExistsExpr>(existsExpr);
  ref<Expr> body = expr->body;

  assert(llvm::isa<AndExpr>(body));

  std::map<ref<Expr>, ref<Expr> > substitution;
  ref<Expr> equalities = body->getKid(1);
  getSubstitution(expr->variables, equalities, substitution);

  ref<Expr> interpolant =
      TxSubstitutionVisitor(substitution).visit(body->getKid(0));

  if (hasVariableInSet(expr->variables, equalities)) {
    // we could also replace the occurrence of some variables with its
    // corresponding substitution mapping.
    equalities = TxSubstitutionVisitor(substitution).visit(equalities);
    equalities = removeUnsubstituted(expr->variables, equalities);
  }

  ref<Expr> newBody = AndExpr::create(interpolant, equalities);

  // FIXME: Need to test the performance of the following.
  if (!hasVariableInSet(expr->variables, newBody))
    return newBody;

  // ref<Expr> ret =
  // simplifyArithmeticBody(existsExpr->rebuild(&newBody),hasExistentialsOnly);
  ref<Expr> ret = existsExpr->rebuild(&newBody);
  return ret;
}

void TxSubsumptionTableEntry::interpolateValues(
    ExecutionState &state, std::set<ref<TxStateValue> > &coreValues,
    std::map<ref<TxStateValue>, std::set<uint64_t> > &corePointerValues,
    int debugSubsumptionLevel) {
  std::string reason = "";
  if (debugSubsumptionLevel >= 1) {
    llvm::raw_string_ostream stream(reason);
    llvm::Instruction *instr = state.pc->inst;
    stream << "subsumption at ";
    if (instr->getParent()->getParent()) {
      std::string functionName(
          instr->getParent()->getParent()->getName().str());
      stream << functionName << ": ";
      if (llvm::MDNode *n = instr->getMetadata("dbg")) {
        llvm::DILocation loc(n);
        stream << "Line " << loc.getLineNumber();
      } else {
        instr->print(stream);
      }
    } else {
      instr->print(stream);
    }
  }

  for (std::set<ref<TxStateValue> >::iterator it = coreValues.begin(),
                                              ie = coreValues.end();
       it != ie; ++it) {
    state.txTreeNode->valuesInterpolation(*it, reason);
  }

#ifdef ENABLE_Z3
  if (TxDependency::boundInterpolation() && !ExactAddressInterpolant) {
    reason = "interpolating memory bound for " + reason;

    for (std::map<ref<TxStateValue>, std::set<uint64_t> >::iterator
             it = corePointerValues.begin(),
             ie = corePointerValues.end();
         it != ie; ++it) {
      bool memoryError = state.txTreeNode->pointerValuesInterpolation(
          it->first, it->second, reason);
      assert(!memoryError && "interpolation should not result in memory error");
    }
  }
#endif
}

bool TxSubsumptionTableEntry::subsumed(
    TimingSolver *solver, ExecutionState &state, double timeout,
    bool leftRetrieval, TxStore::TopStateStore &__internalStore,
    TxStore::LowerStateStore &__concretelyAddressedHistoricalStore,
    TxStore::LowerStateStore &__symbolicallyAddressedHistoricalStore,
    int debugSubsumptionLevel) {
#ifdef ENABLE_Z3

  if (MarkGlobal) {
    // Global check
    bool globalSat = true;
    for (std::set<ref<TxStoreEntry> >::iterator it = markedGlobal.begin(),
                                                ie = markedGlobal.end();
         it != ie; ++it) {
      if ((*it)->getValue()->getType()->isPointerTy() ||
          (*it)->getValue()->getType()->getTypeID() == 0) {
        continue;
      }

      ref<Expr> addr = (*it)->getAddress()->getAddress();
      ref<Expr> offset = (*it)->getAddress()->getOffset();
      unsigned type = (*it)->getAddress()->getSize();
      ObjectPair initOp;
      bool initResolve = TxTree::initialStateCopy->addressSpace.resolveOne(
          cast<klee::ConstantExpr>(addr), initOp);

      ObjectPair currentOp;
      bool currentResolve = state.addressSpace.resolveOne(
          cast<klee::ConstantExpr>(addr), currentOp);

      if (!initResolve || !currentResolve) {
        globalSat = false;
        break;
      } else {
        const ObjectState *initOs = initOp.second;
        ref<Expr> initValue = initOs->read(offset, type * 8);
        const ObjectState *currentOs = currentOp.second;
        ref<Expr> currentValue = currentOs->read(offset, type * 8);

        if (initValue != currentValue) {
          globalSat = false;
          break;
        }
      }
    }

    if (!globalSat) {
      if (debugSubsumptionLevel >= 1) {
        klee_message("#%lu=>#%lu: Global check fail",
                     state.txTreeNode->getNodeSequenceNumber(),
                     nodeSequenceNumber);
      }
      return false;
    } else {
      if (debugSubsumptionLevel >= 1) {
        klee_message("#%lu=>#%lu: Global check success",
                     state.txTreeNode->getNodeSequenceNumber(),
                     nodeSequenceNumber);
      }
    }
  }

  // WP interpolant check
  if (WPInterpolant && !wpInterpolant.isNull()) {
    // Checking if weakest pre-condition holds. In case WPInterpolant
    // flag is set, this serves as the first check when subsuming a node.
    // If it fails then false is returned. If it succeeds then the
    // second check is performed.
    ref<Expr> wpInstantiatedInterpolant =
        state.txTreeNode->instantiateWPatSubsumption(
            wpInterpolant, state.txTreeNode->getDependency());

    if (wpInstantiatedInterpolant.isNull()) {
      if (debugSubsumptionLevel >= 1) {
        klee_message("#%lu=>#%lu: WP check filed, WP instantiation failed",
                     state.txTreeNode->getNodeSequenceNumber(),
                     nodeSequenceNumber);
      }
      return false;
    }

    ref<Expr> wpBoolean =
        ZExtExpr::create(wpInstantiatedInterpolant, Expr::Bool);

    Solver::Validity result;
    std::vector<ref<Expr> > unsatCore;
    bool success = solver->evaluate(state, wpBoolean, result, unsatCore);

    if (!success || result != Solver::True) {
      if (debugSubsumptionLevel >= 1) {
        klee_message("#%lu=>#%lu: Check failure at WP Expr check ",
                     state.txTreeNode->getNodeSequenceNumber(),
                     nodeSequenceNumber);
      }
      return false;
    }
    if (debugSubsumptionLevel >= 1) {
      klee_message("#%lu=>#%lu: Weakest precondition check success",
                   state.txTreeNode->getNodeSequenceNumber(),
                   nodeSequenceNumber);
    }
  }

  // PhiNode Check 1 (checking previous BB is the same at subsumption point)
  if (isa<llvm::PHINode>(state.pc->inst) &&
      prevProgramPoint != reinterpret_cast<uintptr_t>(state.prevPC->inst)) {
    if (debugSubsumptionLevel >= 1) {
      std::string msg;
      std::string padding(makeTabs(1));
      llvm::raw_string_ostream stream(msg);
      stream.flush();
      klee_message("#%lu=>#%lu: Check failure due to different predessor for "
                   "the PHInode.",
                   state.txTreeNode->getNodeSequenceNumber(),
                   nodeSequenceNumber);
    }
    return false;
  }

  // PhiNode Check 2 (checking the value of phi instructions at subsumption
  // point)
  for (std::map<llvm::Value *, std::vector<ref<Expr> > >::const_iterator it =
           phiValues.begin();
       it != phiValues.end(); ++it) {
    if (isa<llvm::PHINode>((*it).first)) {
      llvm::Instruction *phi = dyn_cast<llvm::Instruction>((*it).first);
      std::vector<ref<Expr> > values = (*it).second;
      if (values.empty())
        continue;
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 0)
      llvm::Value *inputArg = phi->getOperand(state.incomingBBIndex);
#else
      llvm::Value *inputArg = phi->getOperand(state.incomingBBIndex * 2);
#endif

      if (state.txTreeNode->getParent() &&
          state.txTreeNode->getParent()->getDependency()) {
        std::map<llvm::Value *, std::vector<ref<TxStateValue> > > valuesMap =
            state.txTreeNode->getParent()->getDependency()->getvaluesMap();
        std::vector<ref<TxStateValue> > txStateVal =
            valuesMap[dyn_cast<llvm::Value>(inputArg)];
        if (txStateVal.empty()) {
          if (debugSubsumptionLevel >= 1) {
            std::string msg;
            std::string padding(makeTabs(1));
            llvm::raw_string_ostream stream(msg);
            stream.flush();
            klee_message(
                "#%lu=>#%lu: Check failure as in PHInode: txStateVal is "
                "empty. Failing conservatively. ",
                state.txTreeNode->getNodeSequenceNumber(), nodeSequenceNumber);
          }
          return false;
        }
        if (txStateVal.back()->getExpression().compare(values.back()) != 0) {
          if (debugSubsumptionLevel >= 1) {
            std::string msg;
            std::string padding(makeTabs(1));
            llvm::raw_string_ostream stream(msg);
            stream.flush();
            klee_message("#%lu=>#%lu: Check failure as in PHInode: phi values "
                         "don't match ",
                         state.txTreeNode->getNodeSequenceNumber(),
                         nodeSequenceNumber);
          }
          return false;
        }
      } else {
        if (debugSubsumptionLevel >= 1) {
          std::string msg;
          std::string padding(makeTabs(1));
          llvm::raw_string_ostream stream(msg);
          stream.flush();
          klee_message("#%lu=>#%lu: Check failure as in PHInode: parent node "
                       "doen't exist. Failing conservatively. ",
                       state.txTreeNode->getNodeSequenceNumber(),
                       nodeSequenceNumber);
        }
        return false;
      }
    } else {
      if (debugSubsumptionLevel >= 1) {
        std::string msg;
        std::string padding(makeTabs(1));
        llvm::raw_string_ostream stream(msg);
        stream.flush();
        klee_message(
            "#%lu=>#%lu: Check failure as this part of PHInode check is not "
            "implemented yet. Failing conservatively. ",
            state.txTreeNode->getNodeSequenceNumber(), nodeSequenceNumber);
      }
      return false;
    }
  }

  // Tell the solver implementation that we are checking for subsumption for
  // collecting statistics of solver calls.
  SubsumptionCheckMarker subsumptionCheckMarker;

  // Quick check for subsumption in case the interpolant is empty
  if (empty()) {
    if (debugSubsumptionLevel >= 1) {
      klee_message("#%lu=>#%lu: Check success due to empty table entry",
                   state.txTreeNode->getNodeSequenceNumber(),
                   nodeSequenceNumber);
    }

    if (WPInterpolant) {
      // In case a node is subsumed, the WP Expr is stored at the parent node.
      // This is crucial for generating WP Expr at the parent node.
      state.txTreeNode->setWPatSubsumption(wpInterpolant);
    }
    return true;
  }

  ref<Expr> stateEqualityConstraints;

  // Translation of allocation in the current state into an allocation in the
  // tabled interpolant. This translation is used to equate absolute address
  // values for allocations of matching sizes.
  std::map<ref<TxAllocationInfo>, ref<TxAllocationInfo> > unifiedBases;

  // Non-pointer / exact pointer values to be marked as in the interpolant
  std::set<ref<TxStateValue> > coreValues;

  // Pointer values in the core for memory bounds interpolation.
  std::map<ref<TxStateValue>, std::set<uint64_t> > corePointerValues;

  {
    TimerStatIncrementer t(concretelyAddressedStoreExpressionBuildTime);

    // Build constraints from concrete-address interpolant store
    for (TxStore::TopInterpolantStore::const_iterator
             it1 = concretelyAddressedStore.begin(),
             ie1 = concretelyAddressedStore.end();
         it1 != ie1; ++it1) {
      assert(!it1->second.empty() && "empty table entry with real index");

      const TxStore::LowerInterpolantStore &tabledConcreteMap = it1->second;
      TxStore::TopStateStore::iterator mIt = __internalStore.find(it1->first);
      if (mIt == __internalStore.end()) {
        if (debugSubsumptionLevel >= 1) {
          std::string msg;
          std::string padding(makeTabs(1));
          llvm::raw_string_ostream stream(msg);
          it1->first->print(stream, padding);
          stream.flush();
          klee_message("#%lu=>#%lu: Check failure as allocated memory region "
                       "in the table does not exist in the state:\n%s",
                       state.txTreeNode->getNodeSequenceNumber(),
                       nodeSequenceNumber, msg.c_str());
        }
        return false;
      }

      TxStore::MiddleStateStore &m = mIt->second;

      for (TxStore::LowerInterpolantStore::const_iterator
               it2 = tabledConcreteMap.begin(),
               ie2 = tabledConcreteMap.end();
           it2 != ie2; ++it2) {
        ref<TxInterpolantValue> stateValue;

        ref<TxStoreEntry> e = m.findConcrete(it2->first, unifiedBases);

        if (e.isNull()) {
          // Fail the subsumption, since the address was not found in the state,
          // and we could not translate the addresses
          if (debugSubsumptionLevel >= 1) {
            std::string msg;
            std::string padding(makeTabs(1));
            llvm::raw_string_ostream stream(msg);
            it2->first->print(stream, padding);
            stream.flush();
            klee_message("#%lu=>#%lu: Check failure as memory region in the "
                         "table does not exist in the state:\n%s",
                         state.txTreeNode->getNodeSequenceNumber(),
                         nodeSequenceNumber, msg.c_str());
          }
          return false;
        } else {
          bool leftUse =
              state.txTreeNode->getStore()->isInLeftSubtree(e->getDepth());
          stateValue = e->getInterpolantStyleValue(leftUse);
        }

        const ref<TxInterpolantValue> tabledValue = it2->second;
        ref<Expr> res;

        if (!stateValue.isNull()) {
          // There is the corresponding concrete allocation
          if (tabledValue->getExpression()->getWidth() !=
              stateValue->getExpression()->getWidth()) {
            // We conservatively fail the subsumption in case the sizes do not
            // match.
            if (debugSubsumptionLevel >= 1) {
              std::string msg;
              klee_message("#%lu=>#%lu: Check failure as sizes of stored "
                           "values do not match%s",
                           state.txTreeNode->getNodeSequenceNumber(),
                           nodeSequenceNumber, msg.c_str());
            }
            return false;
          } else if (TxDependency::boundInterpolation() &&
                     tabledValue->isPointer() && stateValue->isPointer()) {
            ref<Expr> boundsCheck;
            if (!ExactAddressInterpolant && tabledValue->useBound()) {
              std::set<uint64_t> bounds;
              boundsCheck = tabledValue->getBoundsCheck(
                  stateValue, bounds, unifiedBases, debugSubsumptionLevel);
              if (!boundsCheck.isNull()) {
                if (boundsCheck->isFalse()) {
                  if (debugSubsumptionLevel >= 1) {
                    std::string msg;
                    klee_message("#%lu=>#%lu: Check failure due to failure in "
                                 "memory bounds check%s",
                                 state.txTreeNode->getNodeSequenceNumber(),
                                 nodeSequenceNumber, msg.c_str());
                  }
                  return false;
                }
                if (!boundsCheck->isTrue())
                  res = boundsCheck;

                // We record the LLVM value of the pointer
                corePointerValues[stateValue->getOriginalValue()] = bounds;
              }
            }

            if (boundsCheck.isNull()) {
              ref<Expr> offsetsCheck = tabledValue->getOffsetsCheck(
                  stateValue, unifiedBases, debugSubsumptionLevel);

              if (offsetsCheck->isFalse()) {
                if (debugSubsumptionLevel >= 1) {
                  std::string msg;
                  klee_message("#%lu=>#%lu: Check failure due to failure in "
                               "offset equality check%s",
                               state.txTreeNode->getNodeSequenceNumber(),
                               nodeSequenceNumber, msg.c_str());
                }
                return false;
              }
              if (!offsetsCheck->isTrue())
                res = offsetsCheck;

              // We record the value of the pointer for interpolation marking
              coreValues.insert(stateValue->getOriginalValue());
            }
          } else {
            res = EqExpr::create(tabledValue->getExpression(),
                                 stateValue->getExpression());
            if (res->isFalse()) {
              if (debugSubsumptionLevel >= 1) {
                if (debugSubsumptionLevel >= 2) {
                  std::string msg;
                  llvm::raw_string_ostream stream(msg);
                  tabledValue->getExpression()->print(stream);
                  stream << " (interpolant) vs. ";
                  stateValue->getExpression()->print(stream);
                  stream << " (state)";
                  stream.flush();
                  klee_message(
                      "#%lu=>#%lu: Check failure due to unequal content: %s",
                      state.txTreeNode->getNodeSequenceNumber(),
                      nodeSequenceNumber, msg.c_str());
                } else {
                  klee_message(
                      "#%lu=>#%lu: Check failure due to unequal content",
                      state.txTreeNode->getNodeSequenceNumber(),
                      nodeSequenceNumber);
                }

                if (debugSubsumptionLevel >= 3) {
                  std::string msg;
                  llvm::raw_string_ostream stream1(msg);

                  it2->first->print(stream1, makeTabs(1));
                  stream1.flush();

                  klee_message("with value stored in address:\n%s",
                               msg.c_str());
                }
              }
              return false;
            } else if (res->isTrue()) {
              if (debugSubsumptionLevel >= 1) {
                if (debugSubsumptionLevel >= 2) {
                  std::string msg;
                  llvm::raw_string_ostream stream(msg);
                  tabledValue->getExpression()->print(stream);
                  stream.flush();
                  klee_message("#%lu=>#%lu: Equal contents: %s",
                               state.txTreeNode->getNodeSequenceNumber(),
                               nodeSequenceNumber, msg.c_str());
                } else {
                  klee_message("#%lu=>#%lu: Equal contents",
                               state.txTreeNode->getNodeSequenceNumber(),
                               nodeSequenceNumber);
                }

                if (debugSubsumptionLevel >= 3) {
                  std::string msg3;
                  llvm::raw_string_ostream stream1(msg3);

                  it2->first->print(stream1, makeTabs(1));
                  stream1.flush();

                  klee_message("with value stored in address:\n%s",
                               msg3.c_str());
                }
              }
            }
            coreValues.insert(stateValue->getOriginalValue());
          }
        }

        e = m.findSymbolic(it2->first);
        if (!e.isNull()) {
          const ref<Expr> tabledConcreteOffset = it2->first->getOffset();
          ref<Expr> conjunction;
          bool leftUse =
              state.txTreeNode->getStore()->isInLeftSubtree(e->getDepth());

          // We make sure the context part of the addresses (the allocation
          // site and the call history) are equivalent.
          if (it2->first->getContext() == e->getAddress()->getContext()) {

            ref<TxInterpolantValue> interpolantValue =
                e->getInterpolantStyleValue(leftUse);
            ref<Expr> constraint = makeConstraint(
                state, it2->second, interpolantValue, it2->first->getOffset(),
                e->getAddress()->getOffset(), coreValues, corePointerValues,
                unifiedBases, debugSubsumptionLevel);

            if (constraint.isNull())
              return false;

            if (!conjunction.isNull()) {
              conjunction = AndExpr::create(constraint, conjunction);
            } else {
              conjunction = constraint;
            }
          }

          // If there were corresponding concrete as well as symbolic
          // allocations in the current state, conjunct them
          if (!conjunction.isNull()) {
            res = (!res.isNull() ? AndExpr::create(res, conjunction)
                                 : conjunction);
          }
        }

        if (!res.isNull()) {
          stateEqualityConstraints =
              (stateEqualityConstraints.isNull()
                   ? res
                   : AndExpr::create(res, stateEqualityConstraints));
        }
      }
    }

    //------------------------------------------------------------------------
    // Historical concretely-addressed store
    //------------------------------------------------------------------------
    for (TxStore::LowerInterpolantStore::const_iterator
             it1 = concretelyAddressedHistoricalStore.begin(),
             ie1 = concretelyAddressedHistoricalStore.end();
         it1 != ie1; ++it1) {
      TxStore::LowerStateStore::const_iterator mIt =
          __concretelyAddressedHistoricalStore.find(it1->first);
      ref<Expr> constraint;

      if (mIt == __concretelyAddressedHistoricalStore.end()) {
        mIt = __symbolicallyAddressedHistoricalStore.find(it1->first);
        if (mIt != __symbolicallyAddressedHistoricalStore.end()) {
          ref<TxStoreEntry> e = mIt->second;
          bool leftUse =
              state.txTreeNode->getStore()->isInLeftSubtree(e->getDepth());
          ref<TxInterpolantValue> interpolantValue =
              e->getInterpolantStyleValue(leftUse);
          constraint = makeConstraint(
              state, it1->second, interpolantValue, it1->first->getOffset(),
              e->getAddress()->getOffset(), coreValues, corePointerValues,
              unifiedBases, debugSubsumptionLevel);
          if (constraint.isNull())
            return false;
          if (stateEqualityConstraints.isNull()) {
            stateEqualityConstraints = constraint;
          } else {
            stateEqualityConstraints =
                AndExpr::create(constraint, stateEqualityConstraints);
          }
        } else {
          // Match not found
          return false;
        }
      } else {
        ref<TxStoreEntry> e = mIt->second;
        bool leftUse =
            state.txTreeNode->getStore()->isInLeftSubtree(e->getDepth());
        ref<TxInterpolantValue> interpolantValue =
            e->getInterpolantStyleValue(leftUse);
        constraint = makeConstraint(
            state, it1->second, interpolantValue, it1->first->getOffset(),
            e->getAddress()->getOffset(), coreValues, corePointerValues,
            unifiedBases, debugSubsumptionLevel);
        if (constraint.isNull())
          return false;
        if (stateEqualityConstraints.isNull()) {
          stateEqualityConstraints = constraint;
        } else {
          stateEqualityConstraints =
              AndExpr::create(constraint, stateEqualityConstraints);
        }
      }

      if (stateEqualityConstraints.isNull()) {
        stateEqualityConstraints = constraint;
      } else {
        stateEqualityConstraints =
            AndExpr::create(constraint, stateEqualityConstraints);
      }
    }
  }

  {
    TimerStatIncrementer t(symbolicallyAddressedStoreExpressionBuildTime);
    // Build constraints from symbolic-address interpolant store
    for (TxStore::TopInterpolantStore::const_iterator
             it1 = symbolicallyAddressedStore.begin(),
             ie1 = symbolicallyAddressedStore.end();
         it1 != ie1; ++it1) {
      assert(!it1->second.empty() && "empty table entry with real index");

      const TxStore::LowerInterpolantStore &tabledSymbolicMap = it1->second;
      TxStore::TopStateStore::iterator mIt = __internalStore.find(it1->first);
      if (mIt == __internalStore.end()) {
        if (debugSubsumptionLevel >= 1) {
          std::string msg;
          std::string padding(makeTabs(1));
          llvm::raw_string_ostream stream(msg);
          it1->first->print(stream, padding);
          stream.flush();
          klee_message("#%lu=>#%lu: Check failure as allocated memory region "
                       "in the table does not exist in the state:\n%s",
                       state.txTreeNode->getNodeSequenceNumber(),
                       nodeSequenceNumber, msg.c_str());
        }
        return false;
      }

      TxStore::MiddleStateStore &m = mIt->second;

      ref<Expr> conjunction;

      for (TxStore::LowerInterpolantStore::const_iterator
               it2 = tabledSymbolicMap.begin(),
               ie2 = tabledSymbolicMap.end();
           it2 != ie2; ++it2) {

        ref<TxStoreEntry> e = m.findConcrete(it2->first, unifiedBases);
        if (!e.isNull()) {
          bool leftUse =
              state.txTreeNode->getStore()->isInLeftSubtree(e->getDepth());

          // We make sure the context part of the addresses (the allocation site
          // and the call history) are equivalent.
          if (it2->first->getContext() == e->getAddress()->getContext()) {
            ref<TxInterpolantValue> interpolantValue =
                e->getInterpolantStyleValue(leftUse);
            ref<Expr> constraint = makeConstraint(
                state, it2->second, interpolantValue, it2->first->getOffset(),
                e->getAddress()->getOffset(), coreValues, corePointerValues,
                unifiedBases, debugSubsumptionLevel);

            if (constraint.isNull())
              return false;

            if (!constraint.isNull()) {
              if (!conjunction.isNull()) {
                conjunction = AndExpr::create(constraint, conjunction);
              } else {
                conjunction = constraint;
              }
            }
          }
        }

        e = m.findSymbolic(it2->first);
        if (!e.isNull()) {
          bool leftUse =
              state.txTreeNode->getStore()->isInLeftSubtree(e->getDepth());

          // We make sure the context part of the addresses (the allocation site
          // and the call history) are equivalent.
          if (it2->first->getContext() == e->getAddress()->getContext()) {
            ref<TxInterpolantValue> interpolantValue =
                e->getInterpolantStyleValue(leftUse);
            ref<Expr> constraint = makeConstraint(
                state, it2->second, interpolantValue, it2->first->getOffset(),
                e->getAddress()->getOffset(), coreValues, corePointerValues,
                unifiedBases, debugSubsumptionLevel);

            if (constraint.isNull())
              return false;

            if (!conjunction.isNull()) {
              conjunction = AndExpr::create(constraint, conjunction);
            } else {
              conjunction = constraint;
            }
          }
        }
      }

      if (!conjunction.isNull()) {
        stateEqualityConstraints =
            (stateEqualityConstraints.isNull()
                 ? conjunction
                 : AndExpr::create(conjunction, stateEqualityConstraints));
      }
    }

    //------------------------------------------------------------------------
    // Historical symbolically-addressed store
    //------------------------------------------------------------------------
    for (TxStore::LowerInterpolantStore::const_iterator
             it1 = symbolicallyAddressedHistoricalStore.begin(),
             ie1 = symbolicallyAddressedHistoricalStore.end();
         it1 != ie1; ++it1) {

      TxStore::LowerStateStore::const_iterator mIt =
          __concretelyAddressedHistoricalStore.find(it1->first);
      ref<Expr> constraint;

      if (mIt == __concretelyAddressedHistoricalStore.end()) {
        mIt = __symbolicallyAddressedHistoricalStore.find(it1->first);
        if (mIt != __symbolicallyAddressedHistoricalStore.end()) {
          ref<TxStoreEntry> e = mIt->second;
          bool leftUse =
              state.txTreeNode->getStore()->isInLeftSubtree(e->getDepth());
          ref<TxInterpolantValue> interpolantValue =
              e->getInterpolantStyleValue(leftUse);
          constraint = makeConstraint(
              state, it1->second, interpolantValue, it1->first->getOffset(),
              e->getAddress()->getOffset(), coreValues, corePointerValues,
              unifiedBases, debugSubsumptionLevel);
          if (constraint.isNull())
            return false;
          if (stateEqualityConstraints.isNull()) {
            stateEqualityConstraints = constraint;
          } else {
            stateEqualityConstraints =
                AndExpr::create(constraint, stateEqualityConstraints);
          }
        } else {
          // Match not found
          return false;
        }
      } else {
        ref<TxStoreEntry> e = mIt->second;
        bool leftUse =
            state.txTreeNode->getStore()->isInLeftSubtree(e->getDepth());
        ref<TxInterpolantValue> interpolantValue =
            e->getInterpolantStyleValue(leftUse);
        constraint = makeConstraint(
            state, it1->second, interpolantValue, it1->first->getOffset(),
            e->getAddress()->getOffset(), coreValues, corePointerValues,
            unifiedBases, debugSubsumptionLevel);
        if (constraint.isNull())
          return false;
        if (stateEqualityConstraints.isNull()) {
          stateEqualityConstraints = constraint;
        } else {
          stateEqualityConstraints =
              AndExpr::create(constraint, stateEqualityConstraints);
        }
      }
    }
  }

  Solver::Validity result;
  ref<Expr> expr; // The query expression

  {
    TimerStatIncrementer t(solverAccessTime);

    // Here we build the query expression, after which it is always a
    // conjunction of the interpolant and the state equality constraints. Here
    // we call AndExpr::alloc instead of AndExpr::create as we need to guarantee
    // that the resulting expression is an AndExpr, otherwise simplifyExistsExpr
    // would not work.
    if (!interpolant.isNull()) {
      expr = !stateEqualityConstraints.isNull()
                 ? AndExpr::alloc(interpolant, stateEqualityConstraints)
                 : AndExpr::alloc(interpolant,
                                  ConstantExpr::create(1, Expr::Bool));
    } else if (!stateEqualityConstraints.isNull()) {
      expr = AndExpr::alloc(ConstantExpr::create(1, Expr::Bool),
                            stateEqualityConstraints);
    } else {
      // Here both the interpolant constraints and state equality
      // constraints are empty, therefore everything gets subsumed
      if (debugSubsumptionLevel >= 1) {
        std::string msg = "";
        if (!corePointerValues.empty()) {
          msg += " (with successful memory bound checks)";
        }
        klee_message("#%lu=>#%lu: Check success as interpolant is empty%s",
                     state.txTreeNode->getNodeSequenceNumber(),
                     nodeSequenceNumber, msg.c_str());
      }

      interpolateValues(state, coreValues, corePointerValues,
                        debugSubsumptionLevel);
      if (WPInterpolant) {
        // In case a node is subsumed, the WP Expr is stored at the parent node.
        // This is crucial for generating WP Expr at the parent node.
        state.txTreeNode->setWPatSubsumption(wpInterpolant);
      }
      return true;
    }

    bool exprHasNoFreeVariables = false;

    if (!existentials.empty()) {
      ref<Expr> existsExpr = ExistsExpr::create(existentials, expr);
      if (debugSubsumptionLevel >= 2) {
        klee_message("Before simplification:\n%s",
                     TxPrettyExpressionBuilder::constructQuery(
                         state.constraints, existsExpr).c_str());
      }
      expr = simplifyExistsExpr(existsExpr, exprHasNoFreeVariables);
    }

    // We finally simplify the conjunction using create()
    if (llvm::isa<AndExpr>(expr))
      expr = AndExpr::create(expr->getKid(0), expr->getKid(1));

    // If query expression simplification result was false, we quickly fail
    // without calling the solver
    if (expr->isFalse()) {
      if (debugSubsumptionLevel >= 1) {
        klee_message("#%lu=>#%lu: Check failure as consequent is unsatisfiable",
                     state.txTreeNode->getNodeSequenceNumber(),
                     nodeSequenceNumber);
      }
      return false;
    }

    bool success = false;

    if (!detectConflictPrimitives(state, expr)) {
      if (debugSubsumptionLevel >= 1) {
        klee_message(
            "#%lu=>#%lu: Check failure as contradictory equalities detected",
            state.txTreeNode->getNodeSequenceNumber(), nodeSequenceNumber);
      }
      return false;
    }

    std::vector<ref<Expr> > unsatCore;

    // We call the solver only when the simplified query expression is not a
    // constant and no contradictory unary constraints found from
    // solvingUnaryConstraints method.
    if (!llvm::isa<ConstantExpr>(expr)) {
      if (!existentials.empty() && llvm::isa<ExistsExpr>(expr)) {
        if (debugSubsumptionLevel >= 2) {
          klee_message("Existentials not empty");
        }

        if (exprHasNoFreeVariables) {
          // In case the query expression has no free variables, subsumption
          // check succeeds, as the tabled interpolant with
          // existentially-quantified variables was constructed from satisfiable
          // path.

          if (debugSubsumptionLevel >= 1) {
            std::string msg = "";
            if (!corePointerValues.empty()) {
              msg += " (with successful memory bound checks)";
            }
            klee_message("#%lu=>#%lu: Check success as query expression "
                         "contains only bound variables%s",
                         state.txTreeNode->getNodeSequenceNumber(),
                         nodeSequenceNumber, msg.c_str());
          }
          if (WPInterpolant) {
            // In case a node is subsumed, the WP Expr is stored at the parent
            // node. This is crucial for generating WP Expr at the parent node.
            state.txTreeNode->setWPatSubsumption(wpInterpolant);
          }
          return true;
        } else {
          // Here we try to get bound-variables-free conjunction, if there is
          // no constraint with both bound and non-bound variables
          if (ExistsExpr *existsExpr = llvm::dyn_cast<ExistsExpr>(expr)) {
            ref<Expr> boundFree(getBoundFreeConjunction(existsExpr->variables,
                                                        existsExpr->getKid(0)));

            if (!boundFree.isNull()) {
              expr = boundFree;
            }
          }

          if (debugSubsumptionLevel >= 2) {
            klee_message("Querying for subsumption check:\n%s",
                         TxPrettyExpressionBuilder::constructQuery(
                             state.constraints, expr).c_str());
          }

          if (llvm::isa<ExistsExpr>(expr)) {
            // We instantiate a new Z3 solver to make sure that we use Z3
            // without pre-solving optimizations. It would be nice in the future
            // to just run solver->evaluate so that the optimizations can be
            // used, but this requires handling of quantified expressions by
            // KLEE's pre-solving procedure, which does not exist currently.
            Z3Solver *z3solver = new Z3Solver();
            z3solver->setCoreSolverTimeout(timeout);
            success = z3solver->directComputeValidity(
                Query(state.constraints, expr), result, unsatCore);
            z3solver->setCoreSolverTimeout(0);
            delete z3solver;
          } else {
            solver->setTimeout(timeout);
            success = solver->evaluate(state, expr, result, unsatCore);
            solver->setTimeout(0);
          }

          if (!success || result != Solver::True) {
            if (debugSubsumptionLevel >= 1) {
              klee_message("#%lu=>#%lu: Check failure as solved did not decide "
                           "validity of existentially-quantified query",
                           state.txTreeNode->getNodeSequenceNumber(),
                           nodeSequenceNumber);
            }
            return false;
          }
        }

      } else {
        if (debugSubsumptionLevel >= 2) {
          klee_message("Querying for subsumption check:\n%s",
                       TxPrettyExpressionBuilder::constructQuery(
                           state.constraints, expr).c_str());
        }
        // We call the solver in the standard way if the
        // formula is unquantified.
        solver->setTimeout(timeout);
        success = solver->evaluate(state, expr, result, unsatCore);
        solver->setTimeout(0);

        if (!success || result != Solver::True) {
          if (debugSubsumptionLevel >= 1) {
            klee_message(
                "#%lu=>#%lu: Check failure as solved did not decide validity",
                state.txTreeNode->getNodeSequenceNumber(), nodeSequenceNumber);
          }
          return false;
        }
      }
    } else {
      // expr is a constant expression
      if (expr->isTrue()) {
        if (debugSubsumptionLevel >= 1) {
          std::string msg = "";
          if (!corePointerValues.empty()) {
            msg += " (with successful memory bound checks)";
          }
          klee_message(
              "#%lu=>#%lu: Check success as query expression is true%s",
              state.txTreeNode->getNodeSequenceNumber(), nodeSequenceNumber,
              msg.c_str());
        }

        interpolateValues(state, coreValues, corePointerValues,
                          debugSubsumptionLevel);
        if (WPInterpolant) {
          // In case a node is subsumed, the WP Expr is stored at the parent
          // node. This is crucial for generating WP Expr at the parent node.
          state.txTreeNode->setWPatSubsumption(wpInterpolant);
        }
        return true;
      }
      if (debugSubsumptionLevel >= 1) {
        klee_message(
            "#%lu=>#%lu: Check failure as query expression is non-true",
            state.txTreeNode->getNodeSequenceNumber(), nodeSequenceNumber);
      }
      return false;
    }

    // State subsumed, we mark needed constraints on the
    // path condition.
    if (debugSubsumptionLevel >= 1) {
      std::string msg = "";
      if (!corePointerValues.empty()) {
        msg += " (with successful memory bound checks)";
      }
      klee_message("#%lu=>#%lu: Check success as solver decided validity%s",
                   state.txTreeNode->getNodeSequenceNumber(),
                   nodeSequenceNumber, msg.c_str());
    }

    // We create path condition marking structure and mark core constraints
    state.txTreeNode->unsatCoreInterpolation(unsatCore);
    interpolateValues(state, coreValues, corePointerValues,
                      debugSubsumptionLevel);
    if (WPInterpolant) {
      // In case a node is subsumed, the WP Expr is stored at the parent node.
      // This is crucial for generating WP Expr at the parent node.
      state.txTreeNode->setWPatSubsumption(wpInterpolant);
    }
    return true;
  }
#endif /* ENABLE_Z3 */
  return false;
}

ref<Expr> TxSubsumptionTableEntry::getInterpolant() const {
  return interpolant;
}

ref<Expr> TxSubsumptionTableEntry::getWPInterpolant() const {
  return wpInterpolant;
}

TxStore::LowerInterpolantStore
TxSubsumptionTableEntry::getConcretelyAddressedHistoricalStore() const {
  return concretelyAddressedHistoricalStore;
}

TxStore::LowerInterpolantStore
TxSubsumptionTableEntry::getSymbolicallyAddressedHistoricalStore() const {
  return symbolicallyAddressedHistoricalStore;
}

TxStore::TopInterpolantStore
TxSubsumptionTableEntry::getConcretelyAddressedStore() const {
  return concretelyAddressedStore;
}

TxStore::TopInterpolantStore
TxSubsumptionTableEntry::getSymbolicallyAddressedStore() const {
  return symbolicallyAddressedStore;
}

std::set<const Array *> TxSubsumptionTableEntry::getExistentials() const {
  return existentials;
}

void TxSubsumptionTableEntry::setInterpolant(ref<Expr> _interpolant) {
  interpolant = _interpolant;
}

void TxSubsumptionTableEntry::setWPInterpolant(ref<Expr> _wpInterpolant) {
  wpInterpolant = _wpInterpolant;
}

void TxSubsumptionTableEntry::setConcretelyAddressedHistoricalStore(
    TxStore::LowerInterpolantStore _concretelyAddressedHistoricalStore) {
  concretelyAddressedHistoricalStore = _concretelyAddressedHistoricalStore;
}

void TxSubsumptionTableEntry::setSymbolicallyAddressedHistoricalStore(
    TxStore::LowerInterpolantStore _symbolicallyAddressedHistoricalStore) {
  symbolicallyAddressedHistoricalStore = _symbolicallyAddressedHistoricalStore;
}

void TxSubsumptionTableEntry::setConcretelyAddressedStore(
    TxStore::TopInterpolantStore _concretelyAddressedStore) {
  concretelyAddressedStore = _concretelyAddressedStore;
}

void TxSubsumptionTableEntry::setSymbolicallyAddressedStore(
    TxStore::TopInterpolantStore _symbolicallyAddressedStore) {
  symbolicallyAddressedStore = _symbolicallyAddressedStore;
}

void TxSubsumptionTableEntry::setExistentials(
    std::set<const Array *> _existentials) {
  existentials = _existentials;
}

void TxSubsumptionTableEntry::print(llvm::raw_ostream &stream) const {
  print(stream, 0);
}

void TxSubsumptionTableEntry::print(llvm::raw_ostream &stream,
                                    const unsigned paddingAmount) const {
  print(stream, makeTabs(paddingAmount));
}

void TxSubsumptionTableEntry::print(llvm::raw_ostream &stream,
                                    const std::string &prefix) const {
  std::string tabsNext = appendTab(prefix);
  std::string tabsNextNext = appendTab(tabsNext);

  stream << prefix << "------------ Subsumption Table Entry ------------\n";
  stream << prefix << "Program point = " << programPoint << "\n";
  if (MarkGlobal) {
    stream << prefix << "global = [";
    for (std::set<ref<TxStoreEntry> >::iterator it = markedGlobal.begin(),
                                                ie = markedGlobal.end();
         it != ie; ++it) {
      (*it)->print(stream);
    }
    stream << "]\n";
  }
  stream << prefix << "interpolant = ";
  if (!interpolant.isNull())
    interpolant->print(stream);
  else
    stream << "(empty)";

  stream << "\n" << prefix << "concretely-addressed store = [";
  if (!concretelyAddressedStore.empty()) {
    stream << "\n";
    for (TxStore::TopInterpolantStore::const_iterator
             is1 = concretelyAddressedStore.begin(),
             ie1 = concretelyAddressedStore.end(), it1 = is1;
         it1 != ie1; ++it1) {
      for (TxStore::LowerInterpolantStore::const_iterator
               is2 = it1->second.begin(),
               ie2 = it1->second.end(), it2 = is2;
           it2 != ie2; ++it2) {
        if (it1 != is1 || it2 != is2)
          stream << tabsNext << "------------------------------------------\n";
        stream << tabsNext << "address:\n";
        it2->first->print(stream, tabsNextNext);
        stream << "\n";
        stream << tabsNext << "content:\n";
        it2->second->print(stream, tabsNextNext);
        stream << "\n";
      }
    }
    stream << prefix;
  }
  stream << "]";

  stream << "\n" << prefix << "symbolically-addressed store = [";
  if (!symbolicallyAddressedStore.empty()) {
    stream << "\n";
    for (TxStore::TopInterpolantStore::const_iterator
             is1 = symbolicallyAddressedStore.begin(),
             ie1 = symbolicallyAddressedStore.end(), it1 = is1;
         it1 != ie1; ++it1) {
      for (TxStore::LowerInterpolantStore::const_iterator
               is2 = it1->second.begin(),
               ie2 = it1->second.end(), it2 = is2;
           it2 != ie2; ++it2) {
        if (it1 != is1 || it2 != is2)
          stream << tabsNext << "------------------------------------------\n";
        stream << tabsNext << "address:\n";
        it2->first->print(stream, tabsNextNext);
        stream << "\n";
        stream << tabsNext << "content:\n";
        it2->second->print(stream, tabsNextNext);
        stream << "\n";
      }
    }
    stream << prefix;
  }
  stream << "]";

  stream << "\n" << prefix << "concretely-addressed historical store = [";
  if (!concretelyAddressedHistoricalStore.empty()) {
    stream << "\n";
    for (TxStore::LowerInterpolantStore::const_iterator
             is1 = concretelyAddressedHistoricalStore.begin(),
             ie1 = concretelyAddressedHistoricalStore.end(), it1 = is1;
         it1 != ie1; ++it1) {
      if (it1 != is1)
        stream << tabsNext << "------------------------------------------\n";
      stream << tabsNext << "address:\n";
      it1->first->print(stream, tabsNextNext);
      stream << "\n";
      stream << tabsNext << "content:\n";
      it1->second->print(stream, tabsNextNext);
      stream << "\n";
    }
    stream << prefix;
  }
  stream << "]";

  stream << "\n" << prefix << "symbolically-addressed historical store = [";
  if (!symbolicallyAddressedHistoricalStore.empty()) {
    stream << "\n";
    for (TxStore::LowerInterpolantStore::const_iterator
             is1 = symbolicallyAddressedHistoricalStore.begin(),
             ie1 = symbolicallyAddressedHistoricalStore.end(), it1 = is1;
         it1 != ie1; ++it1) {
      if (it1 != is1)
        stream << tabsNext << "------------------------------------------\n";
      stream << tabsNext << "address:\n";
      it1->first->print(stream, tabsNextNext);
      stream << "\n";
      stream << tabsNext << "content:\n";
      it1->second->print(stream, tabsNextNext);
      stream << "\n";
    }
    stream << prefix;
  }
  stream << "]";

  stream << "\n" << prefix << "existentials = [";
  if (!existentials.empty()) {
    for (std::set<const Array *>::const_iterator is = existentials.begin(),
                                                 ie = existentials.end(),
                                                 it = is;
         it != ie; ++it) {
      if (it != is)
        stream << ", ";
      stream << (*it)->name;
    }
  }
  stream << "]";
}

void TxSubsumptionTableEntry::printWP(llvm::raw_ostream &stream) const {
  printWP(stream, 0);
}

void TxSubsumptionTableEntry::printWP(llvm::raw_ostream &stream,
                                      const unsigned paddingAmount) const {
  printWP(stream, makeTabs(paddingAmount));
}

void TxSubsumptionTableEntry::printWP(llvm::raw_ostream &stream,
                                      const std::string &prefix) const {
  stream << prefix << "\nwp interpolant = [";
  if (!wpInterpolant.isNull())
    wpInterpolant->print(stream);
  stream << "]\n";
}

void TxSubsumptionTableEntry::printStat(std::stringstream &stream) {
  stream << "KLEE: done:     Time for actual solver calls in subsumption check "
            "(ms) = " << ((double)stats::subsumptionQueryTime.getValue()) / 1000
         << "\n";
  stream << "KLEE: done:     Number of solver calls for subsumption check "
            "(failed) = " << stats::subsumptionQueryCount.getValue() << " ("
         << stats::subsumptionQueryFailureCount.getValue() << ")\n";
  stream << "KLEE: done:     Concrete store expression build time (ms) = "
         << ((double)concretelyAddressedStoreExpressionBuildTime.getValue()) /
                1000 << "\n";
  stream << "KLEE: done:     Symbolic store expression build time (ms) = "
         << ((double)symbolicallyAddressedStoreExpressionBuildTime.getValue()) /
                1000 << "\n";
  stream << "KLEE: done:     Solver access time (ms) = "
         << ((double)solverAccessTime.getValue()) / 1000 << "\n";
}

/**/

void TxSubsumptionTable::CallHistoryIndexedTable::Node::print(
    llvm::raw_ostream &stream) const {
  print(stream, 0);
}

void TxSubsumptionTable::CallHistoryIndexedTable::Node::print(
    llvm::raw_ostream &stream, const unsigned paddingAmount) const {
  print(stream, makeTabs(paddingAmount));
}

void TxSubsumptionTable::CallHistoryIndexedTable::Node::print(
    llvm::raw_ostream &stream, const std::string &prefix) const {
  std::string tabsNext = appendTab(prefix);

  stream << "\n";
  stream << tabsNext << "Call history-indexed table tree node\n";
  if (id) {
    stream << tabsNext << "node Id = " << reinterpret_cast<uintptr_t>(id)
           << "\n";
  } else {
    stream << tabsNext << "node Id = (root)\n";
  }
  stream << tabsNext << "Entries:\n";
  for (EntryIterator it = entryList.rbegin(), ie = entryList.rend(); it != ie;
       ++it) {
    (*it)->print(stream, tabsNext);
    stream << "\n";
  }
  for (std::map<llvm::Instruction *, Node *>::const_iterator it = next.begin(),
                                                             ie = next.end();
       it != ie; ++it) {
    stream << tabsNext << "Next call:\n";
    it->second->print(stream, appendTab(prefix));
    stream << "\n";
  }
}

/**/

void TxSubsumptionTable::CallHistoryIndexedTable::clearTree(Node *node) {
  for (std::map<llvm::Instruction *, Node *>::iterator it = node->next.begin(),
                                                       ie = node->next.end();
       it != ie; ++it) {
    clearTree(it->second);
    delete it->second;
  }

  for (std::deque<TxSubsumptionTableEntry *>::iterator
           it = node->entryList.begin(),
           ie = node->entryList.end();
       it != ie; ++it) {
    delete (*it);
  }
}

void TxSubsumptionTable::CallHistoryIndexedTable::insert(
    const std::vector<llvm::Instruction *> &callHistory,
    TxSubsumptionTableEntry *entry) {
  Node *current = root;

  for (std::vector<llvm::Instruction *>::const_iterator
           it = callHistory.begin(),
           ie = callHistory.end();
       it != ie; ++it) {
    llvm::Instruction *call = *it;
    std::map<llvm::Instruction *, Node *>::const_iterator it1 =
        current->next.find(call);
    if (it1 == current->next.end()) {
      Node *newNode = new Node(call);
      current->next[*it] = newNode;
      current = newNode;
    } else {
      current = it1->second;
    }
  }
  current->entryList.push_back(entry);
}

std::pair<TxSubsumptionTable::EntryIterator, TxSubsumptionTable::EntryIterator>
TxSubsumptionTable::CallHistoryIndexedTable::find(
    const std::vector<llvm::Instruction *> &callHistory, bool &found) const {
  Node *current = root;
  std::pair<EntryIterator, EntryIterator> ret;

  for (std::vector<llvm::Instruction *>::const_iterator
           it = callHistory.begin(),
           ie = callHistory.end();
       it != ie; ++it) {
    llvm::Instruction *call = *it;
    std::map<llvm::Instruction *, Node *>::const_iterator it1 =
        current->next.find(call);
    if (it1 == current->next.end()) {
      found = false;
      return ret;
    }
    current = it1->second;
  }
  found = true;
  return std::pair<EntryIterator, EntryIterator>(current->entryList.rbegin(),
                                                 current->entryList.rend());
}

void TxSubsumptionTable::CallHistoryIndexedTable::printNode(
    llvm::raw_ostream &stream, Node *n, std::string edges) const {
  for (std::map<llvm::Instruction *, Node *>::const_iterator
           it = n->next.begin(),
           ie = n->next.end();
       it != ie; ++it) {
    stream << "\n";
    it->second->print(stream, edges + "    ");
    stream << "\n";
    printNode(stream, it->second, edges + "    ");
  }
}

void TxSubsumptionTable::CallHistoryIndexedTable::print(
    llvm::raw_ostream &stream) const {
  root->print(stream);
  printNode(stream, root, "");
}

/**/

std::map<uintptr_t, TxSubsumptionTable::CallHistoryIndexedTable *>
TxSubsumptionTable::instance;

void
TxSubsumptionTable::insert(uintptr_t id,
                           const std::vector<llvm::Instruction *> &callHistory,
                           TxSubsumptionTableEntry *entry) {
  CallHistoryIndexedTable *subTable = 0;

  TxTree::entryNumber++; // Count of entries in the table

  std::map<uintptr_t, CallHistoryIndexedTable *>::iterator it =
      instance.find(id);

  if (it == instance.end()) {
    subTable = new CallHistoryIndexedTable();
    subTable->insert(callHistory, entry);
    instance[id] = subTable;
    return;
  }
  subTable = it->second;
  subTable->insert(callHistory, entry);
}

bool TxSubsumptionTable::check(TimingSolver *solver, ExecutionState &state,
                               double timeout, int debugSubsumptionLevel) {
  CallHistoryIndexedTable *subTable = 0;
  TxTreeNode *txTreeNode = state.txTreeNode;

  std::map<uintptr_t, CallHistoryIndexedTable *>::iterator it =
      instance.find(state.txTreeNode->getProgramPoint());
  if (it == instance.end()) {
    if (debugSubsumptionLevel >= 1) {
      klee_message(
          "#%lu: Check failure due to control point not found in table",
          state.txTreeNode->getNodeSequenceNumber());
    }
    return false;
  }
  subTable = it->second;

  bool found;
  std::pair<EntryIterator, EntryIterator> iterPair =
      subTable->find(txTreeNode->entryCallHistory, found);
  if (!found) {
    if (debugSubsumptionLevel >= 1) {
      klee_message("#%lu: Check failure due to entry not found",
                   state.txTreeNode->getNodeSequenceNumber());
    }
    return false;
  }

  if (iterPair.first != iterPair.second) {

    TxStore::TopInterpolantStore concretelyAddressedStore;
    TxStore::TopInterpolantStore symbolicallyAddressedStore;
    TxStore::LowerInterpolantStore concretelyAddressedHistoricalStore;
    TxStore::LowerInterpolantStore symbolicallyAddressedHistoricalStore;

    bool leftRetrieval;
    TxStore::TopStateStore __internalStore;
    TxStore::LowerStateStore __concretelyAddressedHistoricalStore;
    TxStore::LowerStateStore __symbolicallyAddressedHistoricalStore;

    txTreeNode->getStoredExpressions(txTreeNode->entryCallHistory,
                                     leftRetrieval, __internalStore,
                                     __concretelyAddressedHistoricalStore,
                                     __symbolicallyAddressedHistoricalStore);

    // Iterate the subsumption table entry with reverse iterator because
    // the successful subsumption mostly happen in the newest entry.
    for (EntryIterator it = iterPair.first, ie = iterPair.second; it != ie;
         ++it) {
      if ((*it)->subsumed(solver, state, timeout, leftRetrieval,
                          __internalStore, __concretelyAddressedHistoricalStore,
                          __symbolicallyAddressedHistoricalStore,
                          debugSubsumptionLevel)) {
        // We mark as subsumed such that the node will not be
        // stored into table (the table already contains a more
        // general entry).
        txTreeNode->isSubsumed = true;

        // Mark the node as subsumed, and create a subsumption edge
        TxTreeGraph::markAsSubsumed(txTreeNode, (*it));
        return true;
      }
    }
  }
  return false;
}

bool TxSubsumptionTable::hasInterpolation(ExecutionState &state) {

  CallHistoryIndexedTable *subTable = 0;
  TxTreeNode *txTreeNode = state.txTreeNode;

  std::map<uintptr_t, CallHistoryIndexedTable *>::iterator it =
      instance.find(state.txTreeNode->getProgramPoint());
  if (it == instance.end()) {
    return false;
  }
  subTable = it->second;

  bool found;
  subTable->find(txTreeNode->entryCallHistory, found);
  if (!found) {
    return false;
  }

  return true;
}

void TxSubsumptionTable::clear() {
  for (std::map<uintptr_t, CallHistoryIndexedTable *>::iterator
           it = instance.begin(),
           ie = instance.end();
       it != ie; ++it) {
    if (it->second) {
      ++TxTree::programPointNumber;
      delete it->second;
    }
  }
}

/**/

Statistic TxTree::setCurrentINodeTime("SetCurrentINodeTime",
                                      "SetCurrentINodeTime");
Statistic TxTree::removeTime("RemoveTime", "RemoveTime");
Statistic TxTree::subsumptionCheckTime("SubsumptionCheckTime",
                                       "SubsumptionCheckTime");
Statistic TxTree::markPathConditionTime("MarkPathConditionTime", "MarkPCTime");
Statistic TxTree::splitTime("SplitTime", "SplitTime");
Statistic TxTree::executeOnNodeTime("ExecuteOnNodeTime", "ExecuteOnNodeTime");
Statistic TxTree::executeMemoryOperationTime("ExecuteMemoryOperationTime",
                                             "ExecuteMemoryOperationTime");

double TxTree::entryNumber;

double TxTree::programPointNumber;

bool TxTree::symbolicExecutionError = false;

uint64_t TxTree::subsumptionCheckCount = 0;

ExecutionState *TxTree::initialStateCopy = 0;

uint64_t TxTree::blockCount = 1;

void TxTree::printTimeStat(std::stringstream &stream) {
  stream << "KLEE: done:     setCurrentINode = "
         << ((double)setCurrentINodeTime.getValue()) / 1000 << "\n";
  stream << "KLEE: done:     remove = " << ((double)removeTime.getValue()) /
                                               1000 << "\n";
  stream << "KLEE: done:     subsumptionCheck = "
         << ((double)subsumptionCheckTime.getValue()) / 1000 << "\n";
  stream << "KLEE: done:     markPathCondition = "
         << ((double)markPathConditionTime.getValue()) / 1000 << "\n";
  stream << "KLEE: done:     split = " << ((double)splitTime.getValue()) / 1000
         << "\n";
  stream << "KLEE: done:     executeOnNode = "
         << ((double)executeOnNodeTime.getValue()) / 1000 << "\n";
  stream << "KLEE: done:     executeMemoryOperation = "
         << ((double)executeMemoryOperationTime.getValue()) / 1000 << "\n";
}

void TxTree::printTableStat(std::stringstream &stream) {
  TxSubsumptionTableEntry::printStat(stream);

  stream
      << "KLEE: done:     Average table entries per subsumption checkpoint = "
      << inTwoDecimalPoints(entryNumber / programPointNumber) << "\n";

  stream << "KLEE: done:     Number of subsumption checks = "
         << subsumptionCheckCount << "\n";

  stream << "KLEE: done:     Average solver calls per subsumption check = "
         << inTwoDecimalPoints((double)stats::subsumptionQueryCount /
                               (double)subsumptionCheckCount) << "\n";
}

std::string TxTree::inTwoDecimalPoints(const double n) {
  std::ostringstream stream;
  unsigned long x = (unsigned)((n - ((unsigned)n)) * 100);
  unsigned y = (unsigned)n;
  stream << y << ".";
  if (x > 9)
    stream << x;
  else if (x > 0)
    stream << "0" << x;
  else
    stream << "00";
  return stream.str();
}

std::string TxTree::getInterpolationStat() {
  std::stringstream stream;
  stream << "KLEE: done: Total reduced symbolic execution tree nodes = "
         << TxTreeGraph::nodeCount << "\n";
  stream << "KLEE: done: Total number of visited basic blocks = " << blockCount
         << "\n";
  stream << "\nKLEE: done: Subsumption statistics\n";
  printTableStat(stream);
  stream << "\nKLEE: done: TxTree method execution times (ms):\n";
  printTimeStat(stream);
  stream << "\nKLEE: done: TxTreeNode method execution times (ms):\n";
  TxTreeNode::printTimeStat(stream);
  // printing node count
  return stream.str();
}

TxTree::TxTree(
    ExecutionState *_root, llvm::DataLayout *_targetData,
    std::map<const llvm::GlobalValue *, ref<ConstantExpr> > *_globalAddresses)
    : targetData(_targetData), globalAddresses(_globalAddresses) {
  currentTxTreeNode = 0;
  assert(_targetData && "target data layout not provided");
  if (!_root->txTreeNode) {
    currentTxTreeNode = TxTreeNode::createRoot(_targetData, _globalAddresses);
  }
  root = currentTxTreeNode;
  initialStateCopy = new ExecutionState(*_root);
  ;
}

bool TxTree::subsumptionCheck(TimingSolver *solver, ExecutionState &state,
                              double timeout) {
#ifdef ENABLE_Z3
  assert(state.txTreeNode == currentTxTreeNode);

  // Immediately return if the state's instruction is not the
  // the interpolation node id. The interpolation node id is the
  // first instruction executed of the sequence executed for a state
  // node, typically this the first instruction of a basic block.
  // Subsumption check only matches against this first instruction.
  if (!state.txTreeNode || reinterpret_cast<uintptr_t>(state.pc->inst) !=
                               state.txTreeNode->getProgramPoint())
    return false;

  int debugSubsumptionLevel =
      currentTxTreeNode->dependency->debugSubsumptionLevel;

  if (debugSubsumptionLevel >= 2) {
    klee_message("Subsumption check for Node #%lu, Program Point %lu",
                 state.txTreeNode->getNodeSequenceNumber(),
                 state.txTreeNode->getProgramPoint());
  } else if (debugSubsumptionLevel >= 1) {
    klee_message("Subsumption check for Node #%lu",
                 state.txTreeNode->getNodeSequenceNumber());
  }

  ++subsumptionCheckCount; // For profiling

  TimerStatIncrementer t(subsumptionCheckTime);

  return TxSubsumptionTable::check(solver, state, timeout,
                                   debugSubsumptionLevel);
#endif
  return false;
}

void TxTree::setCurrentINode(ExecutionState &state) {
  TimerStatIncrementer t(setCurrentINodeTime);
  currentTxTreeNode = state.txTreeNode;
  currentTxTreeNode->setProgramPoint(state.pc->inst, state.prevPC->inst);
  if (!currentTxTreeNode->nodeSequenceNumber)
    currentTxTreeNode->nodeSequenceNumber =
        TxTreeNode::nextNodeSequenceNumber++;
  TxTreeGraph::setCurrentNode(state, currentTxTreeNode->nodeSequenceNumber);
}

void TxTree::removeSpeculationFailedNodes(TxTreeNode *node) {
  assert(!node->left && !node->right);
  TxTreeNode *p = node->parent;
  if (p) {
    if (node == p->left) {
      p->left = 0;
    } else {
      assert(node == p->right);
      p->right = 0;
    }
  }
  delete node;
}

void TxTree::remove(ExecutionState *state, TimingSolver *solver, bool dumping) {
#ifdef ENABLE_Z3
  TxTreeNode *node = state->txTreeNode;
  TimerStatIncrementer t(removeTime);
  assert(!node->left && !node->right);
  do {
    TxTreeNode *p = node->parent;

    // Speculation Success
    if (INTERPOLATION_ENABLED && SpecTypeToUse != NO_SPEC &&
        node->isSpeculationNode() && !node->isSpeculationFailedNode() && p &&
        !p->isSpeculationNode()) {
      llvm::BasicBlock *pbb = p->getBasicBlock();
      StatsTracker::increaseEle(pbb, 2, false);
    }

    // As the node is about to be deleted, it must have been completely
    // traversed, hence the correct time to table the interpolant.
    //
    // We don't create an interpolant for an error node of generic error type:
    // This is because a generic error returns no information (true), which
    // should not be used for subsuming.
    if (!dumping && !node->isSubsumed && node->storable &&
        !node->genericEarlyTermination) {
      int debugSubsumptionLevel = node->dependency->debugSubsumptionLevel;

      if (debugSubsumptionLevel >= 2) {
        klee_message("Storing entry for Node #%lu, Program Point %lu",
                     node->getNodeSequenceNumber(), node->getProgramPoint());
      } else if (debugSubsumptionLevel >= 1) {
        klee_message("Storing entry for Node #%lu",
                     node->getNodeSequenceNumber());
      }

      // generate marking and wp interpolant
      TxSubsumptionTableEntry *entry =
          new TxSubsumptionTableEntry(node, node->entryCallHistory);

      //      llvm::errs() << "UpdateSubsumptionTableEntry --- \n";
      //      entry->dump();
      //      llvm::errs() << "--------------------------------\n";
      if (WPInterpolant) {
        ref<Expr> WPExpr = entry->getWPInterpolant();
        if (!WPExpr.isNull()) {
          entry = node->wp->updateSubsumptionTableEntry(entry);
        }
      }
      //      llvm::errs() << "End UpdateSubsumptionTableEntry --- \n";

      TxSubsumptionTable::insert(node->getProgramPoint(),
                                 node->entryCallHistory, entry);

      TxTreeGraph::addTableEntryMapping(node, entry);

      if (debugSubsumptionLevel >= 2) {
        std::string msg;
        llvm::raw_string_ostream out(msg);
        entry->print(out);
        if (WPInterpolant) {
          entry->printWP(out);
        }
        out.flush();
        klee_message("%s", msg.c_str());
      }
    }

    if (p) {
      if (!p->genericEarlyTermination)
        p->genericEarlyTermination = node->genericEarlyTermination;
      if (node == p->left) {
        p->left = 0;
      } else {
        assert(node == p->right);
        p->right = 0;
      }
    }
    delete node;
    node = p;
  } while (node && !node->left && !node->right);
#endif
}

std::pair<TxTreeNode *, TxTreeNode *>
TxTree::split(TxTreeNode *parent, ExecutionState *left, ExecutionState *right) {
  TimerStatIncrementer t(splitTime);
  parent->split(left, right);
  TxTreeGraph::addChildren(parent, parent->left, parent->right);
  std::pair<TxTreeNode *, TxTreeNode *> ret(parent->left, parent->right);
  return ret;
}

void TxTree::markPathCondition(ExecutionState &state,
                               std::vector<ref<Expr> > &unsatCore) {
  TimerStatIncrementer t(markPathConditionTime);
  int debugSubsumptionLevel =
      currentTxTreeNode->dependency->debugSubsumptionLevel;

  llvm::BranchInst *binst =
      llvm::dyn_cast<llvm::BranchInst>(state.prevPC->inst);
  if (binst) {
    ref<Expr> unknownExpression;
    std::string reason = "";
    if (debugSubsumptionLevel >= 1) {
      llvm::raw_string_ostream stream(reason);
      stream << "branch infeasibility [";
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
    currentTxTreeNode->dependency->markAllValues(binst->getCondition(),
                                                 unknownExpression, reason);
  }

  // We create path condition marking structure and mark core constraints
  currentTxTreeNode->unsatCoreInterpolation(unsatCore);
}

void TxTree::executePHI(llvm::Instruction *instr, unsigned incomingBlock,
                        ref<Expr> valueExpr) {
  currentTxTreeNode->dependency->executePHI(instr, incomingBlock,
                                            currentTxTreeNode->callHistory,
                                            valueExpr, symbolicExecutionError);
  symbolicExecutionError = false;
}

void TxTree::executeOnNode(TxTreeNode *node, llvm::Instruction *instr,
                           std::vector<ref<Expr> > &args) {
  TimerStatIncrementer t(executeOnNodeTime);
  node->execute(instr, args, symbolicExecutionError);
  symbolicExecutionError = false;
}

bool TxTree::isSpeculationNode() {
  return currentTxTreeNode->isSpeculationNode();
}

void TxTree::storeSpeculationUnsatCore(TimingSolver *solver,
                                       std::vector<ref<Expr> > unsatCore,
                                       llvm::BranchInst *binst) {
  currentTxTreeNode->storeSpeculationUnsatCore(solver, unsatCore, binst);
}

void TxTree::storeInstruction(KInstruction *instr, unsigned incomingBB) {
  currentTxTreeNode->reverseInstructionList.push_back(
      std::pair<KInstruction *, bool>(instr, 0));
  if (llvm::isa<llvm::PHINode>(instr->inst)) {
    currentTxTreeNode->phiNodeArg.insert(
        std::pair<llvm::Instruction *, unsigned>(instr->inst, incomingBB));
  }
}

void TxTree::markInstruction(KInstruction *instr, bool branchFlag) {
  std::vector<std::pair<KInstruction *, int> >::iterator iter =
      std::find(currentTxTreeNode->reverseInstructionList.begin(),
                currentTxTreeNode->reverseInstructionList.end(),
                std::pair<KInstruction *, int>(instr, 0));
  // Marking all the br instruction that have one branch as infeasible.
  // Other infeasible paths (like the infeasible paths in the internal
  // KLEE function klee_make_symbolic are not tracked by weakest pre-
  // condition approach.
  std::string fname = iter->first->inst->getParent()->getParent()->getName();
  if (isa<llvm::BranchInst>(iter->first->inst) &&
      fname.find("klee_") == std::string::npos &&
      fname.find("tx_") == std::string::npos) {
    if (branchFlag == true)
      iter->second = 1;
    else
      iter->second = 2;
  }
}

void TxTree::printNode(llvm::raw_ostream &stream, TxTreeNode *n,
                       std::string edges) const {
  if (n->left != 0) {
    stream << "\n";
    stream << edges << "+-- L:" << n->left->programPoint;
    if (this->currentTxTreeNode == n->left) {
      stream << " (active)";
    }
    if (n->right != 0) {
      printNode(stream, n->left, edges + "|   ");
    } else {
      printNode(stream, n->left, edges + "    ");
    }
  }
  if (n->right != 0) {
    stream << "\n";
    stream << edges << "+-- R:" << n->right->programPoint;
    if (this->currentTxTreeNode == n->right) {
      stream << " (active)";
    }
    printNode(stream, n->right, edges + "    ");
  }
}

void TxTree::print(llvm::raw_ostream &stream) const {
  stream << "------------------------- TxTree Structure "
            "--------------------------\n";
  stream << this->root->programPoint;
  if (this->root == this->currentTxTreeNode) {
    stream << " (active)";
  }
  this->printNode(stream, this->root, "");
  stream << "\n------------------------- Subsumption Table "
            "-------------------------\n";
  TxSubsumptionTable::print(stream);
}

void TxTree::dump() const { this->print(llvm::errs()); }

/**/

// Statistics
Statistic TxTreeNode::getInterpolantTime("GetInterpolantTime",
                                         "GetInterpolantTime");
Statistic TxTreeNode::getWPInterpolantTime("GetWPInterpolantTime",
                                           "GetWPInterpolantTime");
Statistic TxTreeNode::addConstraintTime("AddConstraintTime",
                                        "AddConstraintTime");
Statistic TxTreeNode::splitTime("SplitTime", "SplitTime");
Statistic TxTreeNode::executeTime("ExecuteTime", "ExecuteTime");
Statistic TxTreeNode::bindCallArgumentsTime("BindCallArgumentsTime",
                                            "BindCallArgumentsTime");
Statistic TxTreeNode::bindReturnValueTime("BindReturnValueTime",
                                          "BindReturnValueTime");
Statistic TxTreeNode::getStoredExpressionsTime("GetStoredExpressionsTime",
                                               "GetStoredExpressionsTime");
Statistic
TxTreeNode::getStoredCoreExpressionsTime("GetStoredCoreExpressionsTime",
                                         "GetStoredCoreExpressionsTime");

// The interpolation tree node sequence number
uint64_t TxTreeNode::nextNodeSequenceNumber = 1;

void TxTreeNode::setPhiValue(llvm::Value *val, ref<Expr> value) {
  if (isa<llvm::Instruction>(val)) {
    llvm::Instruction *instr = dyn_cast<llvm::Instruction>(val);
    phiValues[instr].push_back(value);
  }
}

void TxTreeNode::printTimeStat(std::stringstream &stream) {
  stream << "KLEE: done:     getInterpolant = "
         << ((double)getInterpolantTime.getValue()) / 1000 << "\n";
  if (WPInterpolant)
    stream << "KLEE: done:     get WP Interpolant = "
           << ((double)getWPInterpolantTime.getValue()) / 1000 << "\n";
  stream << "KLEE: done:     addConstraintTime = "
         << ((double)addConstraintTime.getValue()) / 1000 << "\n";
  stream << "KLEE: done:     splitTime = " << ((double)splitTime.getValue()) /
                                                  1000 << "\n";
  stream << "KLEE: done:     execute = " << ((double)executeTime.getValue()) /
                                                1000 << "\n";
  stream << "KLEE: done:     bindCallArguments = "
         << ((double)bindCallArgumentsTime.getValue()) / 1000 << "\n";
  stream << "KLEE: done:     bindReturnValue = "
         << ((double)bindReturnValueTime.getValue()) / 1000 << "\n";
  stream << "KLEE: done:     getStoredExpressions = "
         << ((double)getStoredExpressionsTime.getValue()) / 1000 << "\n";
  stream << "KLEE: done:     getStoredCoreExpressions = "
         << ((double)getStoredCoreExpressionsTime.getValue()) / 1000 << "\n";
}

TxTreeNode::TxTreeNode(
    TxTreeNode *_parent, llvm::DataLayout *_targetData,
    std::map<const llvm::GlobalValue *, ref<ConstantExpr> > *_globalAddresses)
    : parent(_parent), left(0), right(0), programPoint(0), prevProgramPoint(0),
      phiValuesFlag(1), nodeSequenceNumber(0), storable(true),
      graph(_parent ? _parent->graph : 0),
      instructionsDepth(_parent ? _parent->instructionsDepth : 0),
      targetData(_targetData), globalAddresses(_globalAddresses),
      genericEarlyTermination(false), assertionFail(false),
      emitAllErrors(false), isSubsumed(false) {
  if (_parent) {
    entryCallHistory = _parent->callHistory;
    callHistory = _parent->callHistory;
  }

  // Inherit the abstract dependency or NULL
  dependency = new TxDependency(_parent ? _parent->dependency : 0, _targetData,
                                _globalAddresses);

  // Set speculation flag to false
  if (INTERPOLATION_ENABLED && SpecTypeToUse != NO_SPEC) {
    speculationFlag = 0;
    speculationFailed = 0;
    visitedProgramPoints = NULL;
    specTime = NULL;
  }

  // Set the child WP Interpolants to false
  if (WPInterpolant) {
    wp = new TxWeakestPreCondition(this, dependency, _targetData);
    childWPInterpolant[0] = wp->True();
    childWPInterpolant[1] = wp->True();
  }
}

TxTreeNode::~TxTreeNode() {
  if (dependency)
    delete dependency;
  if (WPInterpolant && wp) {
    delete wp;
  }
}

ref<Expr> TxTreeNode::getInterpolant(
    std::set<const Array *> &replacements,
    std::map<ref<Expr>, ref<Expr> > &substitution) const {
  TimerStatIncrementer t(getInterpolantTime);
  ref<Expr> expr = dependency->packInterpolant(replacements, substitution);
  return expr;
}

bool TxTreeNode::isSpeculationNode() { return speculationFlag; }

void TxTreeNode::setSpeculationFlag() { speculationFlag = 1; }

bool TxTreeNode::isSpeculationFailedNode() { return speculationFailed; }

void TxTreeNode::setSpeculationFailed() { speculationFailed = 1; }

void TxTreeNode::storeSpeculationUnsatCore(TimingSolver *solver,
                                           std::vector<ref<Expr> > unsatCore,
                                           llvm::BranchInst *binst) {
  speculationSolver = solver;
  speculationUnsatCore = unsatCore;
  speculationBInst = binst;
}

void TxTreeNode::mark() {
  int debugSubsumptionLevel = this->dependency->debugSubsumptionLevel;

  llvm::BranchInst *binst = speculationBInst;
  if (binst) {
    ref<Expr> unknownExpression;
    std::string reason = "";
    if (debugSubsumptionLevel >= 1) {
      llvm::raw_string_ostream stream(reason);
      stream << "branch infeasibility [";
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
    this->dependency->markAllValues(binst->getCondition(), unknownExpression,
                                    reason);
  }

  // We create path condition marking structure and mark core constraints
  this->unsatCoreInterpolation(this->speculationUnsatCore);
}

ref<Expr> TxTreeNode::generateWPInterpolant() {
  TimerStatIncrementer t(getWPInterpolantTime);

  ref<Expr> expr;
  if (assertionFail && emitAllErrors) {
    expr = wp->False();
  } else if (assertionFail) {
    wp->resetWPExpr();
    // Generate weakest precondition from pathCondition and/or BB instructions
    expr = wp->True();
  } else if (childWPInterpolant[0].isNull() || childWPInterpolant[1].isNull()) {
    expr = childWPInterpolant[0].isNull() ? childWPInterpolant[0]
                                          : childWPInterpolant[1];
  } else if (childWPInterpolant[0] == wp->False() ||
             childWPInterpolant[1] == wp->False()) {
    expr = wp->False();
  } else if (childWPInterpolant[0] == wp->True() &&
             childWPInterpolant[1] == wp->True()) {
    wp->resetWPExpr();
    // Generate weakest precondition from pathCondition and/or BB instructions
    expr = wp->PushUp(reverseInstructionList);
  } else {
    // Get branch condition
    llvm::Instruction *i = reverseInstructionList.back().first->inst;
    if (i->getOpcode() == llvm::Instruction::Br) {
      llvm::BranchInst *br = dyn_cast<llvm::BranchInst>(i);
      if (br->isConditional()) {
        branchCondition = wp->getBrCondition(i);
      }
    }
    if (!branchCondition.isNull()) {
      expr = wp->intersectWPExpr(branchCondition, childWPInterpolant[0],
                                 childWPInterpolant[1]);
      if (!expr.isNull()) {
        wp->setWPExpr(expr);
        // Generate weakest precondition from pathCondition and/or BB
        // instructions
        expr = wp->PushUp(reverseInstructionList);
      }
    } else {
      expr = branchCondition; // expr is null
    }
    expr = Z3Simplification::simplify(expr);
  }

  // set to parent node
  if (parent) {
    //	  llvm::errs() << "Parent Node is " << parent->getNodeSequenceNumber()
    //<< "\n";
    if (parent->left == this) {
      parent->childWPInterpolant[0] = expr;
    } else {
      parent->childWPInterpolant[1] = expr;
    }
  }
  return expr;
}

ref<Expr> TxTreeNode::getChildWPInterpolant(int flag) {
  if (flag == 0)
    return childWPInterpolant[0];
  else
    return childWPInterpolant[1];
}

llvm::Instruction *TxTreeNode::getPreviousInstruction(llvm::PHINode *phi) {
  for (std::vector<std::pair<KInstruction *, int> >::const_reverse_iterator
           it = reverseInstructionList.rbegin(),
           ie = reverseInstructionList.rend();
       it != ie; ++it) {
    if ((*it).first->inst == phi)
      return (*++it).first->inst;
  }
  klee_error(
      "TxTreeNode::getPreviousInstruction: Control should not reach here!");
}

// =========================================================================
// Instantiating WP Expression at Subsumption Point
// =========================================================================
ref<Expr> TxTreeNode::instantiateWPatSubsumption(ref<Expr> wpInterpolant,
                                                 TxDependency *dependency) {

  if (wpInterpolant.isNull())
    return wpInterpolant;

  switch (wpInterpolant->getKind()) {
  case Expr::InvalidKind:
  case Expr::Constant: { return wpInterpolant; }

  case Expr::WPVar: {
    // TODO: Not handling multiple copies of a var in store
    // TxTreeNode::instantiateWPatSubsumption
    ref<WPVarExpr> WPVar = dyn_cast<WPVarExpr>(wpInterpolant);

    ref<TxAllocationContext> alc =
        dependency->getStore()->getAddressofLatestCopyLLVMValue(WPVar->address);

    if (!alc.isNull()) {
      ref<TxStoreEntry> entry;
      entry = dependency->getStore()->find(alc);

      if (!entry.isNull()) {
        if (wpInterpolant->getWidth() ==
            entry->getContent()->getExpression()->getWidth()) {
          return entry->getContent()->getExpression();
        } else {
          ref<Expr> result = ZExtExpr::create(
              entry->getContent()->getExpression(), wpInterpolant->getWidth());
          return result;
        }
      }
    }
    // wpInterpolant->dump();
    // dependency->getStore()->dump();
//    klee_warning(
//        "TxTreeNode::instantiateWPatSubsumption: Instantiation WPVar failed!");
    ref<Expr> dummy;
    return dummy;

    break;
  }

  case Expr::NotOptimized:
  case Expr::Not:
  case Expr::Extract:
  case Expr::ZExt:
  case Expr::SExt: {
    ref<Expr> kids[1];
    kids[0] = instantiateWPatSubsumption(wpInterpolant->getKid(0), dependency);
    if (kids[0].isNull())
      return kids[0];
    else
      return wpInterpolant->rebuild(kids);
  }

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
  case Expr::And:
  case Expr::Or:
  case Expr::Xor:
  case Expr::Shl:
  case Expr::LShr:
  case Expr::AShr: {
    ref<Expr> kids[2];
    kids[0] = instantiateWPatSubsumption(wpInterpolant->getKid(0), dependency);
    kids[1] = instantiateWPatSubsumption(wpInterpolant->getKid(1), dependency);
    if (kids[0].isNull())
      return kids[0];
    if (kids[1].isNull())
      return kids[1];

    return wpInterpolant->rebuild(kids);
  }

  case Expr::Select: {
    ref<Expr> kids[3];
    kids[0] = instantiateWPatSubsumption(wpInterpolant->getKid(0), dependency);
    kids[1] = instantiateWPatSubsumption(wpInterpolant->getKid(1), dependency);
    kids[2] = instantiateWPatSubsumption(wpInterpolant->getKid(2), dependency);
    if (kids[0].isNull())
      return kids[0];
    if (kids[1].isNull())
      return kids[1];
    if (kids[2].isNull())
      return kids[2];
    return wpInterpolant->rebuild(kids);
  }
  case Expr::Upd: {
    ref<Expr> kids[3];
    kids[0] = instantiateWPatSubsumption(wpInterpolant->getKid(0), dependency);
    kids[1] = instantiateWPatSubsumption(wpInterpolant->getKid(1), dependency);
    kids[2] = instantiateWPatSubsumption(wpInterpolant->getKid(2), dependency);
    if (kids[0].isNull())
      return kids[0];
    if (kids[1].isNull())
      return kids[1];
    if (kids[2].isNull())
      return kids[2];
    return wpInterpolant->rebuild(kids);
  }
  case Expr::Sel: {

    ref<Expr> kids[2];
    kids[0] = wpInterpolant->getKid(0);
    kids[1] = instantiateWPatSubsumption(wpInterpolant->getKid(1), dependency);
    if (kids[0].isNull())
      return kids[0];
    if (kids[1].isNull())
      return kids[1];

    if (!isa<ConstantExpr>(kids[1])) {
      ref<Expr> nilexp;
      return nilexp;
      // return SelExpr::create(kids[0], kids[1]);
    }

    ref<WPVarExpr> WPVar = dyn_cast<WPVarExpr>(wpInterpolant->getKid(0));

    ref<TxAllocationContext> alc =
        dependency->getStore()->getAddressofLatestCopyLLVMValue(WPVar->address);

    if (!alc.isNull()) {
      ref<TxStoreEntry> entry;
      ref<Expr> offset = MulExpr::create(
          kids[1],
          UDivExpr::create(
              ConstantExpr::create(kids[0]->getWidth(), kids[1]->getWidth()),
              ConstantExpr::create(8, kids[1]->getWidth())));

      assert(isa<ConstantExpr>(offset) &&
             "TxTreeNode::"
             "instantiateWPatSubsumption, offset is "
             "not a constant value");
      entry = dependency->getStore()->find(alc, offset);

      if (!entry.isNull()) {
        if (wpInterpolant->getWidth() ==
            entry->getContent()->getExpression()->getWidth()) {
          return entry->getContent()->getExpression();
        } else {
          ref<Expr> result = ZExtExpr::create(
              entry->getContent()->getExpression(), wpInterpolant->getWidth());
          return result;
        }
      } else {
        ref<Expr> nullref;
        return nullref;
      }
    } else {
      ref<Expr> nullref;
      return nullref;
    }

    wpInterpolant->dump();
    klee_error("TxTreeNode::instantiateWPatSubsumption: Instantiation at Sel "
               "Expression failed!");
    break;
  }
  default: {
    wpInterpolant->dump();
    klee_error("TxWPHelper::instantiateWPatSubsumption: Expression not "
               "supported yet!");
    return wpInterpolant;
  }
  }
}

void TxTreeNode::setWPatSubsumption(ref<Expr> _wpInterpolant) {
  if (parent) {
    if (parent->left == this) {
      parent->childWPInterpolant[0] = _wpInterpolant;
    } else {
      parent->childWPInterpolant[1] = _wpInterpolant;
    }
  }
}

void TxTreeNode::addConstraint(ref<Expr> &constraint, llvm::Value *condition) {
  TimerStatIncrementer t(addConstraintTime);
  ref<TxPCConstraint> pcConstraint =
      dependency->addConstraint(constraint, condition, callHistory);
  graph->addPathCondition(this, pcConstraint.get(), constraint);
}

void TxTreeNode::split(ExecutionState *leftData, ExecutionState *rightData) {
  TimerStatIncrementer t(splitTime);
  assert(left == 0 && right == 0);
  leftData->txTreeNode = createLeftChild();
  rightData->txTreeNode = createRightChild();
  if (INTERPOLATION_ENABLED && SpecTypeToUse != NO_SPEC &&
      this->speculationFlag) {
    leftData->txTreeNode->setSpeculationFlag();
    leftData->txTreeNode->visitedProgramPoints = this->visitedProgramPoints;
    leftData->txTreeNode->specTime = this->specTime;
    rightData->txTreeNode->setSpeculationFlag();
    rightData->txTreeNode->visitedProgramPoints = this->visitedProgramPoints;
    rightData->txTreeNode->specTime = this->specTime;
  }
}

void TxTreeNode::execute(llvm::Instruction *instr,
                         std::vector<ref<Expr> > &args,
                         bool symbolicExecutionError) {
  TimerStatIncrementer t(executeTime);
  dependency->execute(instr, callHistory, args, symbolicExecutionError);
}

void TxTreeNode::bindCallArguments(llvm::Instruction *site,
                                   std::vector<ref<Expr> > &arguments) {
  TimerStatIncrementer t(bindCallArgumentsTime);
  dependency->bindCallArguments(site, callHistory, arguments);
}

void TxTreeNode::bindReturnValue(llvm::CallInst *site, llvm::Instruction *inst,
                                 ref<Expr> returnValue) {
  // TODO: This is probably where we should simplify
  // the dependency graph by removing callee values.
  TimerStatIncrementer t(bindReturnValueTime);
  dependency->bindReturnValue(site, callHistory, inst, returnValue);
}

void TxTreeNode::getStoredExpressions(
    const std::vector<llvm::Instruction *> &_callHistory, bool &leftRetrieval,
    TxStore::TopStateStore &__internalStore,
    TxStore::LowerStateStore &__concretelyAddressedHistoricalStore,
    TxStore::LowerStateStore &__symbolicallyAddressedHistoricalStore) const {
  TimerStatIncrementer t(getStoredExpressionsTime);
  std::map<ref<Expr>, ref<Expr> > dummySubstitution;
  std::set<const Array *> dummyReplacements;

  // Since a program point index is a first statement in a basic block,
  // the allocations to be stored in subsumption table should be obtained
  // from the parent node.
  if (parent) {
    dependency->getParentStoredExpressions(
        _callHistory, dummySubstitution, dummyReplacements, false,
        leftRetrieval, __internalStore, __concretelyAddressedHistoricalStore,
        __symbolicallyAddressedHistoricalStore);
  }
}

void TxTreeNode::getStoredCoreExpressions(
    const std::vector<llvm::Instruction *> &_callHistory,
    const std::map<ref<Expr>, ref<Expr> > &substitution,
    std::set<const Array *> &replacements,
    TxStore::TopInterpolantStore &concretelyAddressedStore,
    TxStore::TopInterpolantStore &symbolicallyAddressedStore,
    TxStore::LowerInterpolantStore &concretelyAddressedHistoricalStore,
    TxStore::LowerInterpolantStore &symbolicallyAddressedHistoricalStore)
    const {
  TimerStatIncrementer t(getStoredCoreExpressionsTime);

  // Since a program point index is a first statement in a basic block,
  // the allocations to be stored in subsumption table should be obtained
  // from the parent node.
  if (parent) {
    dependency->getParentStoredCoreExpressions(
        _callHistory, substitution, replacements, true,
        concretelyAddressedStore, symbolicallyAddressedStore,
        concretelyAddressedHistoricalStore,
        symbolicallyAddressedHistoricalStore);
  }
}

uint64_t TxTreeNode::getInstructionsDepth() { return instructionsDepth; }

void TxTreeNode::incInstructionsDepth() { ++instructionsDepth; }

void
TxTreeNode::unsatCoreInterpolation(const std::vector<ref<Expr> > &unsatCore) {
  dependency->unsatCoreInterpolation(unsatCore);
}

void TxTreeNode::dump() const {
  llvm::errs() << "------------------------- TxTree Node "
                  "-------------------------------\n";
  this->print(llvm::errs());
  llvm::errs() << "\n";
}

void TxTreeNode::print(llvm::raw_ostream &stream) const {
  this->print(stream, 0);
}

void TxTreeNode::print(llvm::raw_ostream &stream,
                       const unsigned paddingAmount) const {
  std::string tabs = makeTabs(paddingAmount);
  std::string tabsNext = appendTab(tabs);

  stream << tabs << "TxTreeNode\n";
  stream << tabsNext << "node Id = " << programPoint << "\n";
  stream << tabsNext << "Left:\n";
  if (!left) {
    stream << tabsNext << "NULL\n";
  } else {
    left->print(stream, paddingAmount + 1);
    stream << "\n";
  }
  stream << tabsNext << "Right:\n";
  if (!right) {
    stream << tabsNext << "NULL\n";
  } else {
    right->print(stream, paddingAmount + 1);
    stream << "\n";
  }
  stream << tabsNext << "Call history:\n";
  for (std::vector<llvm::Instruction *>::const_reverse_iterator
           it = callHistory.rbegin(),
           ie = callHistory.rend();
       it != ie; ++it) {
    stream << tabsNext;
    (*it)->print(stream);
    stream << "\n";
  }
  if (dependency) {
    stream << tabsNext << "------- Abstract Dependencies ----------\n";
    dependency->print(stream, paddingAmount + 1);
  }
}
