/*
 * Z3Simplification.cpp
 *
 *  Created on: 18 Feb 2019
 *      Author: xuanlinhha
 */

#include "Z3Simplification.h"

using namespace klee;

void Z3Simplification::test() {
  std::cout << "Start test!\n";
  z3::context c;
  z3::goal g(c);
  z3::expr x = c.bool_const("x");
  z3::expr y = c.bool_const("y");
  z3::expr z = c.int_const("z");
  z3::expr e = not(not(x) && not(y));
  std::cout << "e = " << e << "\n";
  visit(e);
  std::cout << "End test!\n";
}

ref<Expr> Z3Simplification::simplify(ref<Expr> txe) {
  if (txe.isNull()) {
    return txe;
  }
  z3::context c;
  std::map<std::string, ref<Expr> > emap;
  z3::expr z3e = c.bool_val(false);
  bool succ = txExpr2z3Expr(z3e, c, txe, emap);
  if (succ) {
    z3e = applyTactic(c, "simplify", z3e);
    z3e = applyTactic(c, "ctx-solver-simplify", z3e);
    ref<Expr> ret = z3Expr2TxExpr(z3e, emap);

    return ret;
  }

  return txe;
}

bool Z3Simplification::txExpr2z3Expr(z3::expr &z3e, z3::context &c,
                                     ref<Expr> txe,
                                     std::map<std::string, ref<Expr> > &emap) {
  if (isaVar(txe)) {
    std::string name = extractVarName(txe);
    unsigned int size = txe->getWidth();
    emap.insert(std::pair<std::string, ref<Expr> >(name, txe));
    switch (size) {
    case Expr::Bool:
    case Expr::Int8: {
      z3e = c.bool_const(name.c_str());
      return true;
    }
    case Expr::Int16:
    case Expr::Int32:
    case Expr::Int64: {
      z3e = c.int_const(name.c_str());
      return true;
    }
    default: {
      txe->dump();
      klee_error(
          "Z3Simplification::txExpr2z3Expr does not support for this type!");
      return false;
    }
    }
  }

  switch (txe->getKind()) {
  case Expr::Constant: {
    int val = dyn_cast<ConstantExpr>(txe)->getAPValue().getSExtValue();
    unsigned int size = txe->getWidth();
    switch (size) {
    case Expr::Bool:
    case Expr::Int8: {
      if (val == 0) {
        z3e = c.bool_val(false);
      } else {
        z3e = c.bool_val(true);
      }
      return true;
    }
    case Expr::Int16:
    case Expr::Int32:
    case Expr::Int64: {
      z3e = c.int_val(val);
      return true;
    }
    default: {
      txe->dump();
      return false;
    }
    }
    break;
  }

  case Expr::Not: {
    z3::expr t = c.bool_val(false);
    bool r = txExpr2z3Expr(t, c, txe->getKid(0), emap);
    if (r) {
      z3e = not(t);
      return true;
    }
    return false;
  }
  case Expr::Eq: {
    z3::expr t1 = c.bool_val(false);
    bool r1 = txExpr2z3Expr(t1, c, txe->getKid(0), emap);
    if (r1) {
      z3::expr t2 = c.bool_val(false);
      bool r2 = txExpr2z3Expr(t2, c, txe->getKid(1), emap);
      if (r2) {
        z3e = (t1 == t2);
        return true;
      }
    }
    return false;
  }
  case Expr::Ne: {
    z3::expr t1 = c.bool_val(false);
    bool r1 = txExpr2z3Expr(t1, c, txe->getKid(0), emap);
    if (r1) {
      z3::expr t2 = c.bool_val(false);
      bool r2 = txExpr2z3Expr(t2, c, txe->getKid(1), emap);
      if (r2) {
        z3e = (t1 != t2);
        return true;
      }
    }
    return false;
  }
  case Expr::Ult:
  case Expr::Slt: {
    z3::expr t1 = c.bool_val(false);
    bool r1 = txExpr2z3Expr(t1, c, txe->getKid(0), emap);
    if (r1) {
      z3::expr t2 = c.bool_val(false);
      bool r2 = txExpr2z3Expr(t2, c, txe->getKid(1), emap);
      if (r2) {
        z3e = (t1 < t2);
        return true;
      }
    }
    return false;
  }
  case Expr::Ule:
  case Expr::Sle: {
    z3::expr t1 = c.bool_val(false);
    bool r1 = txExpr2z3Expr(t1, c, txe->getKid(0), emap);
    if (r1) {
      z3::expr t2 = c.bool_val(false);
      bool r2 = txExpr2z3Expr(t2, c, txe->getKid(1), emap);
      if (r2) {
        z3e = (t1 <= t2);
        return true;
      }
    }
    return false;
  }
  case Expr::Ugt:
  case Expr::Sgt: {
    z3::expr t1 = c.bool_val(false);
    bool r1 = txExpr2z3Expr(t1, c, txe->getKid(0), emap);
    if (r1) {
      z3::expr t2 = c.bool_val(false);
      bool r2 = txExpr2z3Expr(t2, c, txe->getKid(1), emap);
      if (r2) {
        z3e = (t1 > t2);
        return true;
      }
    }
    return false;
  }
  case Expr::Uge:
  case Expr::Sge: {
    z3::expr t1 = c.bool_val(false);
    bool r1 = txExpr2z3Expr(t1, c, txe->getKid(0), emap);
    if (r1) {
      z3::expr t2 = c.bool_val(false);
      bool r2 = txExpr2z3Expr(t2, c, txe->getKid(1), emap);
      if (r2) {
        z3e = (t1 >= t2);
        return true;
      }
    }
    return false;
  }

  case Expr::Add: {
    z3::expr t1 = c.bool_val(false);
    bool r1 = txExpr2z3Expr(t1, c, txe->getKid(0), emap);
    if (r1) {
      z3::expr t2 = c.bool_val(false);
      bool r2 = txExpr2z3Expr(t2, c, txe->getKid(1), emap);
      if (r2) {
        z3e = (t1 + t2);
        return true;
      }
    }
    return false;
  }
  case Expr::Sub: {
    z3::expr t1 = c.bool_val(false);
    bool r1 = txExpr2z3Expr(t1, c, txe->getKid(0), emap);
    if (r1) {
      z3::expr t2 = c.bool_val(false);
      bool r2 = txExpr2z3Expr(t2, c, txe->getKid(1), emap);
      if (r2) {
        z3e = (t1 - t2);
        return true;
      }
    }
    return false;
  }
  case Expr::Mul: {
    z3::expr t1 = c.bool_val(false);
    bool r1 = txExpr2z3Expr(t1, c, txe->getKid(0), emap);
    if (r1) {
      z3::expr t2 = c.bool_val(false);
      bool r2 = txExpr2z3Expr(t2, c, txe->getKid(1), emap);
      if (r2) {
        z3e = (t1 * t2);
        return true;
      }
    }
    return false;
  }
  case Expr::UDiv:
  case Expr::SDiv: {
    z3::expr t1 = c.bool_val(false);
    bool r1 = txExpr2z3Expr(t1, c, txe->getKid(0), emap);
    if (r1) {
      z3::expr t2 = c.bool_val(false);
      bool r2 = txExpr2z3Expr(t2, c, txe->getKid(1), emap);
      if (r2) {
        z3e = (t1 / t2);
        return true;
      }
    }
    return false;
  }
  case Expr::URem:
  case Expr::SRem: {
    z3::expr t1 = c.bool_val(false);
    bool r1 = txExpr2z3Expr(t1, c, txe->getKid(0), emap);
    if (r1) {
      z3::expr t2 = c.bool_val(false);
      bool r2 = txExpr2z3Expr(t2, c, txe->getKid(1), emap);
      if (r2) {
        z3e = rem(t1, t2);
        return true;
      }
    }
    return false;
  }
  case Expr::And: {
    z3::expr t1 = c.bool_val(false);
    bool r1 = txExpr2z3Expr(t1, c, txe->getKid(0), emap);
    if (r1) {
      z3::expr t2 = c.bool_val(false);
      bool r2 = txExpr2z3Expr(t2, c, txe->getKid(1), emap);
      if (r2) {
        z3e = (t1 && t2);
        return true;
      }
    }
    return false;
  }
  case Expr::Or: {
    z3::expr t1 = c.bool_val(false);
    bool r1 = txExpr2z3Expr(t1, c, txe->getKid(0), emap);
    if (r1) {
      z3::expr t2 = c.bool_val(false);
      bool r2 = txExpr2z3Expr(t2, c, txe->getKid(1), emap);
      if (r2) {
        z3e = (t1 || t2);
        return true;
      }
    }
    return false;
  }
  case Expr::Xor: {
    z3::expr t1 = c.bool_val(false);
    bool r1 = txExpr2z3Expr(t1, c, txe->getKid(0), emap);
    if (r1) {
      z3::expr t2 = c.bool_val(false);
      bool r2 = txExpr2z3Expr(t2, c, txe->getKid(1), emap);
      if (r2) {
        z3e = not(not(t2) && not(t1));
        return true;
      }
    }
    return false;
  }

  default: {
    // Sanity check
    //    klee_warning("Cannot convert to z3 with type: %d", txe->getKind());
    return false;
  }
  }
}

ref<Expr>
Z3Simplification::z3Expr2TxExpr(z3::expr e,
                                std::map<std::string, ref<Expr> > &emap) {
  if (e.is_const()) {
    std::string name = e.decl().name().str();
    if (name == "Int") {
      if (e.get_numeral_int() < 0) {
        int absVal = abs(e.get_numeral_int());
        ref<ConstantExpr> val = ConstantExpr::create(absVal, Expr::Int32);
        return SubExpr::create(ConstantExpr::create(0, Expr::Int32), val);

      } else {
        ref<ConstantExpr> val =
            ConstantExpr::create(e.get_numeral_int(), Expr::Int32);
        return val;
      }
    } else if (name == "true") {
      ref<ConstantExpr> val = ConstantExpr::create(1, Expr::Bool);
      return val;
    } else if (name == "false") {
      ref<ConstantExpr> val = ConstantExpr::create(0, Expr::Bool);
      return val;
    } else { // lookup in emap
      std::map<std::string, ref<Expr> >::iterator i = emap.find(name);
      if (i != emap.end()) {
        return i->second;
      } else {
        klee_error("Z3Simplification::z3Expr2TxExpr: var is not in emap!");
      }
    }
  } else if (e.is_app()) {
    std::string symbol = e.decl().name().str();
    if (symbol == "+") {
      unsigned size = e.num_args();
      ref<Expr> childs[size];
      // convert
      for (unsigned i = 0; i < size; ++i) {
        childs[i] = z3Expr2TxExpr(e.arg(i), emap);
      }
      // find max len
      unsigned max = childs[0]->getWidth();
      for (unsigned i = 1; i < size; ++i) {
        if (childs[i]->getWidth() > max) {
          max = childs[i]->getWidth();
        }
      }
      // extend to make lens equal
      for (unsigned i = 0; i < size; ++i) {
        childs[i] = (childs[i]->getWidth() == max)
                        ? childs[i]
                        : ZExtExpr::create(childs[i], max);
      }
      // and all

      ref<Expr> tmp = AddExpr::create(childs[0], childs[1]);
      for (unsigned i = 2; i < size; ++i) {
        tmp = AddExpr::create(tmp, childs[i]);
      }
      return tmp;
    } else if (symbol == "-") {
      ref<Expr> l = z3Expr2TxExpr(e.arg(0), emap);
      ref<Expr> r = z3Expr2TxExpr(e.arg(1), emap);
      unsigned max =
          l->getWidth() > r->getWidth() ? l->getWidth() : r->getWidth();
      l = (l->getWidth() == max) ? l : ZExtExpr::create(l, max);
      r = (r->getWidth() == max) ? r : ZExtExpr::create(r, max);
      return SubExpr::create(l, r);
    } else if (symbol == "*") {
      ref<Expr> l = z3Expr2TxExpr(e.arg(0), emap);
      ref<Expr> r = z3Expr2TxExpr(e.arg(1), emap);
      unsigned max =
          l->getWidth() > r->getWidth() ? l->getWidth() : r->getWidth();
      l = (l->getWidth() == max) ? l : ZExtExpr::create(l, max);
      r = (r->getWidth() == max) ? r : ZExtExpr::create(r, max);
      return MulExpr::create(l, r);
    } else if (symbol == "div") {
      ref<Expr> l = z3Expr2TxExpr(e.arg(0), emap);
      ref<Expr> r = z3Expr2TxExpr(e.arg(1), emap);
      return SDivExpr::create(l, r);
    } else if (symbol == "rem" || symbol == "mod") {
      ref<Expr> l = z3Expr2TxExpr(e.arg(0), emap);
      ref<Expr> r = z3Expr2TxExpr(e.arg(1), emap);
      return SRemExpr::create(l, r);
    } else if (symbol == "=") {
      ref<Expr> l = z3Expr2TxExpr(e.arg(0), emap);
      ref<Expr> r = z3Expr2TxExpr(e.arg(1), emap);
      unsigned max =
          l->getWidth() > r->getWidth() ? l->getWidth() : r->getWidth();
      l = (l->getWidth() == max) ? l : ZExtExpr::create(l, max);
      r = (r->getWidth() == max) ? r : ZExtExpr::create(r, max);
      return EqExpr::create(l, r);
    } else if (symbol == "<=") {
      ref<Expr> l = z3Expr2TxExpr(e.arg(0), emap);
      ref<Expr> r = z3Expr2TxExpr(e.arg(1), emap);
      unsigned max =
          l->getWidth() > r->getWidth() ? l->getWidth() : r->getWidth();
      l = (l->getWidth() == max) ? l : ZExtExpr::create(l, max);
      r = (r->getWidth() == max) ? r : ZExtExpr::create(r, max);
      return SleExpr::create(l, r);
    } else if (symbol == "<") {
      ref<Expr> l = z3Expr2TxExpr(e.arg(0), emap);
      ref<Expr> r = z3Expr2TxExpr(e.arg(1), emap);
      unsigned max =
          l->getWidth() > r->getWidth() ? l->getWidth() : r->getWidth();
      l = (l->getWidth() == max) ? l : ZExtExpr::create(l, max);
      r = (r->getWidth() == max) ? r : ZExtExpr::create(r, max);
      return SltExpr::create(l, r);
    } else if (symbol == ">=") {
      ref<Expr> l = z3Expr2TxExpr(e.arg(0), emap);
      ref<Expr> r = z3Expr2TxExpr(e.arg(1), emap);
      unsigned max =
          l->getWidth() > r->getWidth() ? l->getWidth() : r->getWidth();
      l = (l->getWidth() == max) ? l : ZExtExpr::create(l, max);
      r = (r->getWidth() == max) ? r : ZExtExpr::create(r, max);
      return SgeExpr::create(l, r);
    } else if (symbol == ">") {
      ref<Expr> l = z3Expr2TxExpr(e.arg(0), emap);
      ref<Expr> r = z3Expr2TxExpr(e.arg(1), emap);
      unsigned max =
          l->getWidth() > r->getWidth() ? l->getWidth() : r->getWidth();
      l = (l->getWidth() == max) ? l : ZExtExpr::create(l, max);
      r = (r->getWidth() == max) ? r : ZExtExpr::create(r, max);
      return SgtExpr::create(l, r);
    } else if (symbol == "not") {
      ref<Expr> left = z3Expr2TxExpr(e.arg(0), emap);
      return NotExpr::create(left);
    } else if (symbol == "and") {
      ref<Expr> f = z3Expr2TxExpr(e.arg(0), emap);
      for (unsigned i = 1; i < e.num_args(); i++) {
        ref<Expr> n = z3Expr2TxExpr(e.arg(i), emap);
        f = AndExpr::create(f, n);
      }
      return f;
    } else if (symbol == "or") {
      ref<Expr> f = z3Expr2TxExpr(e.arg(0), emap);
      for (unsigned i = 1; i < e.num_args(); i++) {
        ref<Expr> n = z3Expr2TxExpr(e.arg(i), emap);
        f = OrExpr::create(f, n);
      }
      return f;
    } else {
      std::cout << e << "\n";
      std::cout << symbol << "\n";
      klee_error("Z3Simplification::z3Expr2TxExpr does not support for this "
                 "type of expr!");
    }
  } else {
    std::cout << e << "\n";
    klee_error("Z3Simplification::z3Expr2TxExpr does not support for this type "
               "of expr!");
  }

  ref<Expr> ret;
  return ret;
}

z3::expr Z3Simplification::applyTactic(z3::context &c, std::string tactic,
                                       z3::expr e) {
  z3::goal g(c);
  g.add(e);
  z3::tactic t(c, tactic.c_str());
  z3::apply_result r = t(g);
  assert(r.size() > 0 && "apply result is empty!");
  z3::expr ret = r[0].as_expr();
  for (unsigned i = 1; i < r.size(); i++) {
    ret = ret || r[i].as_expr();
  }
  return ret;
}

bool Z3Simplification::isaVar(ref<Expr> e) {
  switch (e->getKind()) {
  case Expr::WPVar:
  case Expr::Read:
    return true;

  case Expr::Concat: {
    if (isa<ReadExpr>(e->getKid(0))) {
      return true;
    } else {
      return false;
    }
  }
  default:
    return false;
  }
}

std::string Z3Simplification::extractVarName(ref<Expr> e) {
  assert(isaVar(e) && "Z3Simplification::extractVarName: Not a var!");
  switch (e->getKind()) {
  case Expr::WPVar:
    return dyn_cast<WPVarExpr>(e)->getName();
  case Expr::Read:
    return dyn_cast<ReadExpr>(e)->getName();
  case Expr::Concat:
    return dyn_cast<ReadExpr>(e->getKid(0))->getName();
  default:
    return "";
  }
}
