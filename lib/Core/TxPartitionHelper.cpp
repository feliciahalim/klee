//===-- TxPartitionHelper.cpp - Interpolation tree -------------------------*-
// C++ -*-===//
//
//               The Tracer-X KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// This file contains the implementations Partition class
///
//===----------------------------------------------------------------------===//

#include "TxPartitionHelper.h"

using namespace klee;

std::vector<ref<Expr> > TxPartitionHelper::getExprsFromAndExpr(ref<Expr> e) {
  std::vector<ref<Expr> > ret;
  if (!e.isNull()) {
    if (e->getKind() == Expr::And) {
      std::vector<ref<Expr> > left = getExprsFromAndExpr(e->getKid(0));
      std::vector<ref<Expr> > right = getExprsFromAndExpr(e->getKid(1));
      for (std::vector<ref<Expr> >::iterator it = right.begin(),
                                             ie = right.end();
           it != ie; ++it) {
        left.push_back(*it);
      }
      return left;
    } else {
      ret.push_back(e);
    }
  }
  return ret;
}

std::set<std::string> TxPartitionHelper::getExprVars(ref<Expr> expr) {
  std::set<std::string> vars;

  switch (expr->getKind()) {
  case Expr::InvalidKind:
  case Expr::Constant: {
    return vars;
  }

  case Expr::WPVar: {
    ref<WPVarExpr> WPVar = dyn_cast<WPVarExpr>(expr);
    vars.insert(eliminateShadow(WPVar->name));
    return vars;
  }

  case Expr::Read: {
    ref<ReadExpr> readExpr = dyn_cast<ReadExpr>(expr);
    vars.insert(eliminateShadow(readExpr->getName()));
    return vars;
  }

  case Expr::Concat: {
    ref<ConcatExpr> concatExpr = dyn_cast<ConcatExpr>(expr);
    std::set<std::string> vars1 = getExprVars(concatExpr->getLeft());
    std::set<std::string> vars2 = getExprVars(concatExpr->getRight());
    vars1.insert(vars2.begin(), vars2.end());
    return vars1;
  }

  case Expr::NotOptimized:
  case Expr::Not:
  case Expr::Extract:
  case Expr::ZExt:
  case Expr::SExt: {
    return getExprVars(expr->getKid(0));
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
    std::set<std::string> left = getExprVars(kids[0]);
    std::set<std::string> right = getExprVars(kids[1]);
    left.insert(right.begin(), right.end());
    return left;
  }

  case Expr::Select: {
    std::set<std::string> vars1;
    ref<Expr> kids[2];
    kids[0] = expr->getKid(0);
    if (kids[0]->getKind() != Expr::WPVar) {
      vars1 = getExprVars(kids[0]);
    }
    kids[1] = expr->getKid(1);
    std::set<std::string> vars2 = getExprVars(kids[1]);
    vars1.insert(vars2.begin(), vars2.end());
    return vars1;
  }

  case Expr::Upd: {
    std::set<std::string> vars1;
    ref<Expr> kids[3];
    kids[0] = expr->getKid(0);
    if (kids[0]->getKind() != Expr::WPVar) {
      vars1 = getExprVars(kids[0]);
    }

    kids[1] = expr->getKid(1);
    std::set<std::string> vars2 = getExprVars(kids[1]);
    vars1.insert(vars2.begin(), vars2.end());
    kids[2] = expr->getKid(2);
    std::set<std::string> vars3 = getExprVars(kids[2]);
    vars1.insert(vars3.begin(), vars3.end());
    return vars1;
  }
  case Expr::Sel: {
    ref<Expr> kids[2];
    kids[0] = expr->getKid(0);
    kids[1] = expr->getKid(1);
    std::set<std::string> vars1 = getExprVars(kids[0]);
    std::set<std::string> vars2 = getExprVars(kids[1]);
    vars1.insert(vars2.begin(), vars2.end());
    return vars1;
  }
  default: {
    // Sanity check
    expr->dump();
    klee_error("Control should not reach here in "
               "TxPartitionHelper::getExprVars!");
  }
  }

  return vars;
}

bool TxPartitionHelper::isShared(std::set<std::string> ss1,
                                 std::set<std::string> ss2) {
  for (std::set<std::string>::const_iterator it1 = ss1.begin(), ie1 = ss1.end();
       it1 != ie1; ++it1) {
    for (std::set<std::string>::const_iterator it2 = ss2.begin(),
                                               ie2 = ss2.end();
         it2 != ie2; ++it2) {
      if ((*it2).compare(*it1) == 0) {
        return true;
      }
    }
  }
  return false;
}

bool TxPartitionHelper::isSubset(std::set<std::string> ss1,
                                 std::set<std::string> ss2) {
  for (std::set<std::string>::const_iterator it1 = ss1.begin(), ie1 = ss1.end();
       it1 != ie1; ++it1) {
    int flag = false;
    for (std::set<std::string>::const_iterator it2 = ss2.begin(),
                                               ie2 = ss2.end();
         it2 != ie2; ++it2) {
      if ((*it2).compare(*it1) == 0) {
        flag = true;
      }
    }
    if (flag == false)
      return false;
  }
  return true;
}

std::set<std::string> TxPartitionHelper::diff(std::set<std::string> ss1,
                                              std::set<std::string> ss2) {
  std::set<std::string> diff;
  for (std::set<std::string>::const_iterator it1 = ss1.begin(), ie1 = ss1.end();
       it1 != ie1; ++it1) {
    if (ss2.find(*it1) == ss2.end()) {
      diff.insert(*it1);
    }
  }
  return diff;
}

ref<Expr> TxPartitionHelper::createAnd(std::vector<ref<Expr> > exprs) {
  ref<Expr> result;
  if (exprs.size() == 0) {
    return result;
  }
  std::vector<ref<Expr> >::const_iterator it = exprs.begin();
  result = *(it);
  std::advance(it, 1);
  if (exprs.size() >= 1) {
    for (; it != exprs.end(); ++it) {
      ref<Expr> currentExpr = (*it);
      result = AndExpr::create(result, currentExpr);
    }
  }
  return result;
}

std::string TxPartitionHelper::eliminateShadow(std::string name) {
  if (name.substr(0, 10) == "__shadow__") {
//	llvm::errs() << "__shadow__ found: " << name << "\n";
	return name.substr(10, name.size()-10);
  }
  return name;
}

void TxPartitionHelper::testing(ref<Expr> expr, ExecutionState es) {
  std::set<std::string> readSet = getExprVars(expr);
  llvm::outs() << "=========begin\n";
  es.prevPC->inst->dump();
  for (std::set<std::string>::iterator it = readSet.begin(), ie = readSet.end();
       it != ie; ++it) {
    llvm::outs() << (*it) << "\n";
  }
  llvm::outs() << "=========end\n";
}
