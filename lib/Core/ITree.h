/*
 * ITree.h
 *
 *  Created on: Oct 15, 2015
 *      Author: felicia
 */

#ifndef ITREE_H_
#define ITREE_H_

#include <klee/Expr.h>
#include "klee/Config/Version.h"
#include "klee/ExecutionState.h"

#include "Dependency.h"

#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace klee {
class ExecutionState;

class PathCondition;

class SubsumptionTableEntry;

/// Time records for method running time statistics
class TimeStat {
  double amount;
  double lastRecorded;

public:
  TimeStat() : amount(0.0), lastRecorded(0.0) {}

  ~TimeStat() {}

  void start() {
    if (lastRecorded == 0.0)
      lastRecorded = clock();
  }

  void end() {
    amount += (clock() - lastRecorded);
    lastRecorded = 0.0;
  }

  double get() { return (amount / (double)CLOCKS_PER_SEC); }
};

/// Options for global interpolation mechanism
struct InterpolationOption {

  /// @brief Global variable denoting whether interpolation is enabled or
  /// otherwise
  static bool interpolation;

  /// @brief Output the tree tree.dot in .dot file format
  static bool outputTree;

  /// @brief To display running time statistics of interpolation methods
  static bool timeStat;
};

/// Storage of search tree for displaying
class SearchTree {

  /// @brief counter for the next visited node id
  static unsigned long nextNodeId;

  /// @brief Global search tree instance
  static SearchTree *instance;

  /// Encapsulates functionality of expression builder
  class PrettyExpressionBuilder {

    std::string bvOne() {
      return "1";
    };
    std::string bvZero() {
      return "0";
    };
    std::string bvMinusOne() { return "-1"; }
    std::string bvConst32(uint32_t value);
    std::string bvConst64(uint64_t value);
    std::string bvZExtConst(uint64_t value);
    std::string bvSExtConst(uint64_t value);

    std::string bvBoolExtract(std::string expr, int bit);
    std::string bvExtract(std::string expr, unsigned top, unsigned bottom);
    std::string eqExpr(std::string a, std::string b);

    // logical left and right shift (not arithmetic)
    std::string bvLeftShift(std::string expr, unsigned shift);
    std::string bvRightShift(std::string expr, unsigned shift);
    std::string bvVarLeftShift(std::string expr, std::string shift);
    std::string bvVarRightShift(std::string expr, std::string shift);
    std::string bvVarArithRightShift(std::string expr, std::string shift);

    // Some STP-style bitvector arithmetic
    std::string bvMinusExpr(std::string minuend, std::string subtrahend);
    std::string bvPlusExpr(std::string augend, std::string addend);
    std::string bvMultExpr(std::string multiplacand, std::string multiplier);
    std::string bvDivExpr(std::string dividend, std::string divisor);
    std::string sbvDivExpr(std::string dividend, std::string divisor);
    std::string bvModExpr(std::string dividend, std::string divisor);
    std::string sbvModExpr(std::string dividend, std::string divisor);
    std::string notExpr(std::string expr);
    std::string bvAndExpr(std::string lhs, std::string rhs);
    std::string bvOrExpr(std::string lhs, std::string rhs);
    std::string iffExpr(std::string lhs, std::string rhs);
    std::string bvXorExpr(std::string lhs, std::string rhs);
    std::string bvSignExtend(std::string src);

    // Some STP-style array domain interface
    std::string writeExpr(std::string array, std::string index,
                          std::string value);
    std::string readExpr(std::string array, std::string index);

    // ITE-expression constructor
    std::string iteExpr(std::string condition, std::string whenTrue,
                        std::string whenFalse);

    // Bitvector comparison
    std::string bvLtExpr(std::string lhs, std::string rhs);
    std::string bvLeExpr(std::string lhs, std::string rhs);
    std::string sbvLtExpr(std::string lhs, std::string rhs);
    std::string sbvLeExpr(std::string lhs, std::string rhs);

    std::string existsExpr(std::string body);

    std::string constructAShrByConstant(std::string expr, unsigned shift,
                                        std::string isSigned);
    std::string constructMulByConstant(std::string expr, uint64_t x);
    std::string constructUDivByConstant(std::string expr_n, uint64_t d);
    std::string constructSDivByConstant(std::string expr_n, uint64_t d);

    std::string getInitialArray(const Array *root);
    std::string getArrayForUpdate(const Array *root, const UpdateNode *un);

    std::string constructActual(ref<Expr> e);

    std::string buildArray(const char *name, unsigned indexWidth,
                           unsigned valueWidth);

    std::string getTrue();
    std::string getFalse();
    std::string getInitialRead(const Array *root, unsigned index);

    PrettyExpressionBuilder();

    ~PrettyExpressionBuilder();

  public:
    static std::string construct(ref<Expr> e);
  };

  /// Node information
  class Node {
    friend class SearchTree;

    /// @brief Interpolation tree node id
    uintptr_t iTreeNodeId;

    /// @brief The node id, also the order in which it is traversed
    unsigned long nodeId;

    /// @brief False and true children of this node
    SearchTree::Node *falseTarget, *trueTarget;

    /// @brief Indicates that node is subsumed
    bool subsumed;

    /// @brief Conditions under which this node is visited from its parent
    std::map<PathCondition *, std::pair<std::string, bool> > pathConditionTable;

    /// @brief Human-readable identifier of this node
    std::string name;

    Node(uintptr_t nodeId)
        : iTreeNodeId(nodeId), nodeId(0), falseTarget(0), trueTarget(0),
          subsumed(false) {}

    ~Node() {
      if (falseTarget)
        delete falseTarget;

      if (trueTarget)
        delete trueTarget;

      pathConditionTable.clear();
    }

    static SearchTree::Node *createNode(uintptr_t id) {
      return new SearchTree::Node(id);
    }
  };

  SearchTree::Node *root;
  std::map<ITreeNode *, SearchTree::Node *> itreeNodeMap;
  std::map<SubsumptionTableEntry *, SearchTree::Node *> tableEntryMap;
  std::map<SearchTree::Node *, SearchTree::Node *> subsumptionEdges;
  std::map<PathCondition *, SearchTree::Node *> pathConditionMap;

  static std::string recurseRender(const SearchTree::Node *node);

  std::string render();

  SearchTree(ITreeNode *_root);

  ~SearchTree();

public:
  static void initialize(ITreeNode *root) {
    if (!InterpolationOption::outputTree)
      return;

    if (!instance)
      delete instance;
    instance = new SearchTree(root);
  }

  static void deallocate() {
    if (!InterpolationOption::outputTree)
      return;

    if (!instance)
      delete instance;
    instance = 0;
  }

  static void addChildren(ITreeNode *parent, ITreeNode *falseChild,
                          ITreeNode *trueChild);

  static void setCurrentNode(ExecutionState &state,
                             const uintptr_t programPoint);

  static void markAsSubsumed(ITreeNode *iTreeNode,
                             SubsumptionTableEntry *entry);

  static void addPathCondition(ITreeNode *iTreeNode,
                               PathCondition *pathCondition,
                               ref<Expr> condition);

  static void addTableEntryMapping(ITreeNode *iTreeNode,
                                   SubsumptionTableEntry *entry);

  static void includeInInterpolant(PathCondition *pathCondition);

  /// @brief Save the graph
  static void save(std::string dotFileName);
};

/**/

class PathCondition {
  /// @brief KLEE expression
  ref<Expr> constraint;

  /// @brief KLEE expression with variables (arrays) replaced by their shadows
  ref<Expr> shadowConstraint;

  /// @brief If shadow consraint had been generated: We generate shadow
  /// constraint
  /// on demand only when the constraint is required in an interpolant
  bool shadowed;

  /// @brief The dependency information for the current
  /// interpolation tree node
  Dependency *dependency;

  /// @brief the condition value from which the
  /// constraint was generated
  VersionedValue *condition;

  /// @brief When true, indicates that the constraint should be included
  /// in the interpolant
  bool inInterpolant;

  /// @brief Previous path condition
  PathCondition *tail;

public:
  PathCondition(ref<Expr> &constraint, Dependency *dependency,
                llvm::Value *condition, PathCondition *prev);

  ~PathCondition();

  ref<Expr> car() const;

  PathCondition *cdr() const;

  void includeInInterpolant(AllocationGraph *g);

  bool carInInterpolant() const;

  ref<Expr> packInterpolant(std::vector<const Array *> &replacements);

  void dump();

  void print(llvm::raw_ostream &stream);
};

class PathConditionMarker {
  bool mayBeInInterpolant;

  PathCondition *pathCondition;

public:
  PathConditionMarker(PathCondition *pathCondition);

  ~PathConditionMarker();

  void includeInInterpolant(AllocationGraph *g);

  void mayIncludeInInterpolant();
};

class SubsumptionTableEntry {
  /// @brief Statistics for actual solver call time in subsumption check
  static TimeStat actualSolverCallTime;

  /// @brief The number of solver calls for subsumption checks
  static unsigned long checkSolverCount;

  /// @brief The number of failed solver calls for subsumption checks
  static unsigned long checkSolverFailureCount;

  uintptr_t nodeId;

  ref<Expr> interpolant;

  std::map<llvm::Value *, ref<Expr> > singletonStore;

  std::vector<llvm::Value *> singletonStoreKeys;

  std::map<llvm::Value *, std::vector<ref<Expr> > > compositeStore;

  std::vector<llvm::Value *> compositeStoreKeys;

  std::vector<const Array *> existentials;

  static bool hasExistentials(std::vector<const Array *> &existentials,
                              ref<Expr> expr);

  static ref<Expr> createBinaryOfSameKind(ref<Expr> originalExpr,
                                          ref<Expr> newLhs, ref<Expr> newRhs);

  static bool containShadowExpr(ref<Expr> expr, ref<Expr> shadowExpr);

  static ref<Expr> replaceExpr(ref<Expr> originalExpr, ref<Expr> replacedExpr,
                               ref<Expr> withExpr);

  static ref<Expr>
  simplifyInterpolantExpr(std::vector<ref<Expr> > &interpolantPack,
                          ref<Expr> expr);

  static ref<Expr> simplifyEqualityExpr(std::vector<ref<Expr> > &equalityPack,
                                        ref<Expr> expr);

  static ref<Expr> simplifyWithFourierMotzkin(ref<Expr> existsExpr);

  static ref<Expr> simplifyExistsExpr(ref<Expr> existsExpr);

  static ref<Expr> simplifyArithmeticBody(ref<Expr> existsExpr);

  bool empty() {
    return !interpolant.get() && singletonStoreKeys.empty() &&
           compositeStoreKeys.empty();
  }

  /// @brief for printing method running time statistics
  static void printTimeStat(llvm::raw_ostream &stream);

public:
  SubsumptionTableEntry(ITreeNode *node);

  ~SubsumptionTableEntry();

  bool subsumed(TimingSolver *solver, ExecutionState &state, double timeout);

  void dump() const;

  void print(llvm::raw_ostream &stream) const;

  static void dumpTimeStat();
};

class ITree {
  typedef std::vector<ref<Expr> > ExprList;
  typedef ExprList::iterator iterator;
  typedef ExprList::const_iterator const_iterator;

  static TimeStat setCurrentINodeTime;
  static TimeStat removeTime;
  static TimeStat checkCurrentStateSubsumptionTime;
  static TimeStat markPathConditionTime;
  static TimeStat splitTime;
  static TimeStat executeAbstractBinaryDependencyTime;
  static TimeStat executeAbstractMemoryDependencyTime;
  static TimeStat executeAbstractDependencyTime;

  ITreeNode *currentINode;

  std::vector<SubsumptionTableEntry *> subsumptionTable;

  void printNode(llvm::raw_ostream &stream, ITreeNode *n, std::string edges);

  /// @brief for printing method running time statistics
  static void printTimeStat(llvm::raw_ostream &stream);

public:
  ITreeNode *root;

  ITree(ExecutionState *_root);

  ~ITree();

  std::vector<SubsumptionTableEntry *> getStore();

  void store(SubsumptionTableEntry *subItem);

  void setCurrentINode(ExecutionState &state, uintptr_t programPoint);

  void remove(ITreeNode *node);

  bool checkCurrentStateSubsumption(TimingSolver *solver, ExecutionState &state,
                                    double timeout);

  void markPathCondition(ExecutionState &state, TimingSolver *solver);

  std::pair<ITreeNode *, ITreeNode *>
  split(ITreeNode *parent, ExecutionState *left, ExecutionState *right);

  void executeAbstractBinaryDependency(llvm::Instruction *i,
                                       ref<Expr> valueExpr, ref<Expr> tExpr,
                                       ref<Expr> fExpr);

  void executeAbstractMemoryDependency(llvm::Instruction *instr,
                                       ref<Expr> value, ref<Expr> address);

  void executeAbstractDependency(llvm::Instruction *instr, ref<Expr> value);

  void print(llvm::raw_ostream &stream);

  void dump();

  static void dumpTimeStat();
};

class ITreeNode {
  friend class ITree;

  friend class ExecutionState;

  static TimeStat getInterpolantTime;
  static TimeStat addConstraintTime;
  static TimeStat splitTime;
  static TimeStat makeMarkerMapTime;
  static TimeStat deleteMarkerMapTime;
  static TimeStat executeBinaryDependencyTime;
  static TimeStat executeAbstractMemoryDependencyTime;
  static TimeStat executeAbstractDependencyTime;
  static TimeStat bindCallArgumentsTime;
  static TimeStat popAbstractDependencyFrameTime;
  static TimeStat getLatestCoreExpressionsTime;
  static TimeStat getCompositeCoreExpressionsTime;
  static TimeStat getLatestInterpolantCoreExpressionsTime;
  static TimeStat getCompositeInterpolantCoreExpressionsTime;
  static TimeStat computeInterpolantAllocationsTime;

private:
  typedef ref<Expr> expression_type;

  typedef std::pair<expression_type, expression_type> pair_type;

  /// @brief The path condition
  PathCondition *pathCondition;

  /// @brief Abstract stack for value dependencies
  Dependency *dependency;

  ITreeNode *parent, *left, *right;

  uintptr_t nodeId;

  bool isSubsumed;

  /// @brief Graph for displaying as .dot file
  SearchTree *graph;

  void setNodeLocation(uintptr_t programPoint) {
    if (!nodeId)
      nodeId = programPoint;
  }

  /// @brief for printing method running time statistics
  static void printTimeStat(llvm::raw_ostream &stream);

public:
  uintptr_t getNodeId();

  ref<Expr> getInterpolant(std::vector<const Array *> &replacements) const;

  void addConstraint(ref<Expr> &constraint, llvm::Value *value);

  void split(ExecutionState *leftData, ExecutionState *rightData);

  std::map<ref<Expr>, PathConditionMarker *> makeMarkerMap() const;

  static void
  deleteMarkerMap(std::map<ref<Expr>, PathConditionMarker *> &markerMap);

  void executeBinaryDependency(llvm::Instruction *i, ref<Expr> valueExpr,
                               ref<Expr> tExpr, ref<Expr> fExpr);

  void executeAbstractMemoryDependency(llvm::Instruction *instr,
                                       ref<Expr> value, ref<Expr> address);

  void executeAbstractDependency(llvm::Instruction *instr, ref<Expr> value);

  void bindCallArguments(llvm::Instruction *site,
                         std::vector<ref<Expr> > &arguments);

  void popAbstractDependencyFrame(llvm::CallInst *site, llvm::Instruction *inst,
                                  ref<Expr> returnValue);

  std::map<llvm::Value *, ref<Expr> > getLatestCoreExpressions() const;

  std::map<llvm::Value *, std::vector<ref<Expr> > >
  getCompositeCoreExpressions() const;

  std::map<llvm::Value *, ref<Expr> > getLatestInterpolantCoreExpressions(
      std::vector<const Array *> &replacements) const;

  std::map<llvm::Value *, std::vector<ref<Expr> > >
  getCompositeInterpolantCoreExpressions(
      std::vector<const Array *> &replacements) const;

  void computeInterpolantAllocations(AllocationGraph *g);

  void dump() const;

  void print(llvm::raw_ostream &stream) const;

  static void dumpTimeStat();

private:
  ITreeNode(ITreeNode *_parent);

  ~ITreeNode();

  void print(llvm::raw_ostream &stream, const unsigned tabNum) const;
};
}
#endif /* ITREE_H_ */
