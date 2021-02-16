//===-- TxPartitionHelper.h - Tracer-X symbolic execution tree -------------*-
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
/// This file contains declarations of the classes that support for partitioning
///
//===----------------------------------------------------------------------===//

#ifndef LIB_CORE_TXPARTITIONHELPER_H_
#define LIB_CORE_TXPARTITIONHELPER_H_

#include "TxStore.h"
#include "klee/ExecutionState.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "llvm/IR/Value.h"
#include <iostream>
#include <map>
#include <string>
#include <string.h>

namespace klee {

class TxPartitionHelper {
public:
  static std::vector<ref<Expr> > getExprsFromAndExpr(ref<Expr> e);
  static std::set<std::string> getExprVars(ref<Expr> e);
  static bool isShared(std::set<std::string> ss1, std::set<std::string> ss2);
  static bool isSubset(std::set<std::string> ss1, std::set<std::string> ss2);
  static std::set<std::string> diff(std::set<std::string> ss1,
                                    std::set<std::string> ss2);
  static ref<Expr> createAnd(std::vector<ref<Expr> > exprs);
  static std::string eliminateShadow(std::string name);
  static void testing(ref<Expr> expr, ExecutionState es);
};
}
#endif /* TXLIB_CORE_PARTITIONHELPER_H_ */
