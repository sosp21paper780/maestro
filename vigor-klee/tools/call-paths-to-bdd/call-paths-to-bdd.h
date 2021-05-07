#pragma once

#include "klee/ExprBuilder.h"
#include "klee/perf-contracts.h"
#include "klee/util/ArrayCache.h"
#include "klee/util/ExprSMTLIBPrinter.h"
#include "klee/util/ExprVisitor.h"
#include <klee/Constraints.h>
#include <klee/Solver.h>
#include "llvm/Support/CommandLine.h"

#include <algorithm>
#include <dlfcn.h>
#include <expr/Parser.h>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <regex>
#include <vector>
#include <memory>
#include <stack>
#include <utility>
#include <sstream>

#include "load-call-paths.h"
#include "printer.h"

namespace BDD {

class BDD;

typedef std::pair<call_path_t*, calls_t> call_path_pair_t;

struct call_paths_t {
  std::vector<call_path_t*> cp;
  std::vector<calls_t> backup;

  static std::vector<std::string> skip_functions;

  call_paths_t() {}
  call_paths_t(const call_paths_t& other) : cp(other.cp), backup(other.backup) {}

  call_paths_t(std::vector<call_path_t*> _call_paths)
    : cp(_call_paths) {
    for (const auto& _cp : cp) {
      backup.emplace_back(_cp->calls);
    }

    assert(cp.size() == backup.size());
  }

  size_t size() const {
    return cp.size();
  }

  call_path_pair_t get(unsigned int i) {
    assert(i < size());
    return call_path_pair_t(cp[i], backup[i]);
  }

  void clear() {
    cp.clear();
    backup.clear();
  }

  void push_back(call_path_pair_t pair) {
    cp.push_back(pair.first);
    backup.push_back(pair.second);
  }

  static bool is_skip_function(const std::string& fname);
};

class ReplaceSymbols: public klee::ExprVisitor::ExprVisitor {
private:
  std::vector<klee::ref<klee::ReadExpr>> reads;

  klee::ExprBuilder *builder = klee::createDefaultExprBuilder();
  std::map<klee::ref<klee::Expr>, klee::ref<klee::Expr>> replacements;

public:
  ReplaceSymbols(std::vector<klee::ref<klee::ReadExpr>> _reads)
    : ExprVisitor(true), reads(_reads) {}

  klee::ExprVisitor::Action visitExprPost(const klee::Expr &e) {
    std::map<klee::ref<klee::Expr>, klee::ref<klee::Expr>>::const_iterator it =
        replacements.find(klee::ref<klee::Expr>(const_cast<klee::Expr *>(&e)));

    if (it != replacements.end()) {
      return Action::changeTo(it->second);
    } else {
      return Action::doChildren();
    }
  }

  klee::ExprVisitor::Action visitRead(const klee::ReadExpr &e) {
    klee::UpdateList ul = e.updates;
    const klee::Array *root = ul.root;

    for (const auto& read : reads) {
      if (read->getWidth() != e.getWidth()) {
        continue;
      }

      if (read->index.compare(e.index) != 0) {
        continue;
      }

      if (root->name != read->updates.root->name) {
        continue;
      }

      if (root->getDomain() != read->updates.root->getDomain()) {
        continue;
      }

      if (root->getRange() != read->updates.root->getRange()) {
        continue;
      }

      if (root->getSize() != read->updates.root->getSize()) {
        continue;
      }

      klee::ref<klee::Expr> replaced = klee::expr::ExprHandle(const_cast<klee::ReadExpr *>(&e));
      std::map<klee::ref<klee::Expr>, klee::ref<klee::Expr>>::const_iterator it = replacements.find(replaced);

      if (it != replacements.end()) {
        replacements.insert({ replaced, read });
      }

      return Action::changeTo(read);
    }

    return Action::doChildren();
  }
};


struct solver_toolbox_t {
  klee::Solver *solver;
  klee::ExprBuilder *exprBuilder;

  solver_toolbox_t() {
    solver = klee::createCoreSolver(klee::Z3_SOLVER);
    assert(solver);

    solver = createCexCachingSolver(solver);
    solver = createCachingSolver(solver);
    solver = createIndependentSolver(solver);

    exprBuilder = klee::createDefaultExprBuilder();
  }

  solver_toolbox_t(const solver_toolbox_t& _other)
    : solver(_other.solver), exprBuilder(_other.exprBuilder) {}

  bool is_expr_always_true(klee::ref<klee::Expr> expr) const;
  bool is_expr_always_true(klee::ConstraintManager constraints, klee::ref<klee::Expr> expr) const;
  bool is_expr_always_true(klee::ConstraintManager constraints, klee::ref<klee::Expr> expr, ReplaceSymbols& symbol_replacer) const;

  bool is_expr_always_false(klee::ref<klee::Expr> expr) const;
  bool is_expr_always_false(klee::ConstraintManager constraints, klee::ref<klee::Expr> expr) const;
  bool is_expr_always_false(klee::ConstraintManager constraints, klee::ref<klee::Expr> expr, ReplaceSymbols& symbol_replacer) const;

  bool are_exprs_always_equal(klee::ref<klee::Expr> expr1, klee::ref<klee::Expr> expr2) const;

  uint64_t value_from_expr(klee::ref<klee::Expr> expr) const;
};

class Node {
public:
  enum NodeType {
    BRANCH, CALL, RETURN_INIT, RETURN_PROCESS, RETURN_RAW
  };

protected:
  friend class Call;
  friend class Branch;
  friend class ReturnRaw;
  friend class ReturnInit;
  friend class ReturnProcess;

  uint64_t id;
  NodeType type;

  Node *next;
  Node *prev;

  std::vector<std::string> call_paths_filenames;
  std::vector<calls_t> missing_calls;

  virtual std::string get_gv_name() const {
    std::stringstream ss;
    ss << id;
    return ss.str();
  }

public:
  Node(uint64_t _id, NodeType _type)
    : id(_id), type(_type), next(nullptr), prev(nullptr) {}

  Node(uint64_t _id, NodeType _type, const std::vector<call_path_t*>& _call_paths)
    : id(_id), type(_type), next(nullptr), prev(nullptr) {
    process_call_paths(_call_paths);
  }

  Node(uint64_t _id, NodeType _type, Node *_next, Node *_prev, const std::vector<call_path_t*>& _call_paths)
    : id(_id), type(_type), next(_next), prev(_prev) {
    process_call_paths(_call_paths);
  }

  Node(uint64_t _id, NodeType _type, Node *_next, Node *_prev,
       const std::vector<std::string>& _call_paths_filenames,
       const std::vector<calls_t>& _missing_calls)
    : id(_id), type(_type), next(_next), prev(_prev),
      call_paths_filenames(_call_paths_filenames),
      missing_calls(_missing_calls) {}

  void replace_next(Node* _next) {
    next = _next;
  }

  void add_next(Node* _next) {
    assert(next == nullptr);
    next = _next;
  }

  void replace_prev(Node* _prev) {
    prev = _prev;
  }

  void add_prev(Node* _prev) {
    assert(prev == nullptr);
    prev = _prev;
  }

  const Node* get_next() const {
    return next;
  }

  const Node* get_prev() const {
    return prev;
  }

  NodeType get_type() const {
    return type;
  }

  const std::vector<std::string>& get_call_paths_filenames() const {
    return call_paths_filenames;
  }

  const std::vector<calls_t>& get_missing_calls() const {
    return missing_calls;
  }

  virtual ~Node() {
    if (next) {
      delete next;
    }
  }

  virtual Node* clone() const = 0;
  virtual void dump() const = 0;
  virtual void dump_compact(int lvl=0) const = 0;
  virtual std::string dump_gv() const = 0;

  void process_call_paths(std::vector<call_path_t*> call_paths) {
    std::string dir_delim = "/";
    std::string ext_delim = ".";

    for (const auto& cp : call_paths) {
      missing_calls.emplace_back(cp->calls);
      std::string filename = cp->file_name;

      auto dir_found = filename.find_last_of(dir_delim);
      if (dir_found != std::string::npos) {
        filename = filename.substr(dir_found+1, filename.size());
      }

      auto ext_found = filename.find_last_of(ext_delim);
      if (ext_found != std::string::npos) {
        filename = filename.substr(0, ext_found);
      }

      call_paths_filenames.push_back(filename);
    }
  }
};

class Call : public Node {
private:
  call_t call;

public:
  Call(uint64_t _id, call_t _call, const std::vector<call_path_t*>& _call_paths)
    : Node(_id, Node::NodeType::CALL, _call_paths), call(_call) {}

  Call(uint64_t _id, call_t _call, Node *_next, Node *_prev, const std::vector<call_path_t*>& _call_paths)
    : Node(_id, Node::NodeType::CALL, _next, _prev, _call_paths), call(_call) {}

  Call(uint64_t _id, call_t _call, Node *_next, Node *_prev,
       const std::vector<std::string>& _call_paths_filenames,
       const std::vector<calls_t>& _missing_calls)
    : Node(_id, Node::NodeType::CALL, _next, _prev, _call_paths_filenames, _missing_calls), call(_call) {}

  call_t get_call() const {
    return call;
  }

  virtual Node* clone() const override {
    Call* clone = new Call(id, call, next, prev, call_paths_filenames, missing_calls);
    return clone;
  }

  virtual void dump() const override {
    std::cerr << "===========================================" << "\n";
    std::cerr << "type:      call" << "\n";
    std::cerr << "callpaths: ";
    int i = 0;
    for (const auto& filename : call_paths_filenames) {
      if (i > 0 && i % 5 == 0)  {
        std::cerr << "\n" << "           ";
      }
      if (i > 0 && i % 5 != 0) std::cerr << ", ";
      std::cerr << filename;
      i++;
    }
    std::cerr << "\n";
    std::cerr << "function:  " << call.function_name << "\n";
    std::cerr << "args:      ";
    bool indent = false;
    for (const auto& arg : call.args) {
      if (indent) std::cerr << "           ";
      std::cerr << arg.first << " : "; arg.second.expr->dump();
      indent = true;
    }
    if (!call.ret.isNull()) {
      std::cerr << "ret:       "; call.ret->dump();
    }
    std::cerr << "===========================================" << "\n";
  }

  virtual void dump_compact(int lvl) const override {
    std::string sep = std::string(lvl*2, ' ');
    std::cerr << sep << call.function_name << "\n";
  }

  virtual std::string dump_gv() const override {
    std::stringstream ss;

    if (next) {
      ss << next->dump_gv();
    }

    ss << "\t\t" << get_gv_name();
    ss << " [label=\"";
    ss << call.function_name;
    ss << "(";

    bool first = true;
    for (const auto& pair : call.args) {
      if (!first) {
        ss << ", ";
      } else {
        first = false;
      }

      arg_t arg  = pair.second;
      ss << pretty_print_expr(arg.expr);
    }
    ss << ")\", color=cornflowerblue];\n";

    if (next) {
      ss << "\t\t" << get_gv_name();
      ss << " -> ";
      ss << next->get_gv_name();
      ss << ";\n";
    }

    return ss.str();
  }
};

class Branch : public Node {
private:
  klee::ref<klee::Expr> condition;
  Node *on_false;

public:
  Branch(uint64_t _id, klee::ref<klee::Expr> _condition, const std::vector<call_path_t*>& _call_paths)
    : Node(_id, Node::NodeType::BRANCH, _call_paths),
      condition(_condition), on_false(nullptr) {}

  Branch(uint64_t _id, klee::ref<klee::Expr> _condition, Node *_on_true, Node *_on_false, Node *_prev,
         const std::vector<call_path_t*>& _call_paths)
    : Node(_id, Node::NodeType::BRANCH, _on_true, _prev, _call_paths),
      condition(_condition), on_false(_on_false) {}

  Branch(uint64_t _id, klee::ref<klee::Expr> _condition, Node *_on_true, Node *_on_false, Node *_prev,
         const std::vector<std::string>& _call_paths_filenames,
         const std::vector<calls_t>& _missing_calls)
    : Node(_id, Node::NodeType::BRANCH, _on_true, _prev, _call_paths_filenames, _missing_calls),
      condition(_condition), on_false(_on_false) {}

  klee::ref<klee::Expr> get_condition() const {
    return condition;
  }

  void replace_on_true(Node* _on_true) {
    replace_next(_on_true);
  }

  void add_on_true(Node* _on_true) {
    add_next(_on_true);
  }

  const Node* get_on_true() const {
    return next;
  }

  void replace_on_false(Node* _on_false) {
    on_false = _on_false;
  }

  void add_on_false(Node* _on_false) {
    assert(on_false == nullptr);
    on_false = _on_false;
  }

  const Node* get_on_false() const {
    return on_false;
  }

  ~Branch() {
    if (on_false) {
      delete on_false;
    }
  }

  virtual Node* clone() const override {
    Branch* clone = new Branch(id, condition, next, on_false, prev, call_paths_filenames, missing_calls);
    return clone;
  }

  virtual void dump() const override {
    std::cerr << "===========================================" << "\n";
    std::cerr << "type:      branch" << "\n";
    std::cerr << "condition: "; condition->dump();
    std::cerr << "===========================================" << "\n";
  }

  virtual void dump_compact(int lvl) const override {}

  virtual std::string dump_gv() const override {
    std::stringstream ss;

    if (next) {
      ss << next->dump_gv();
    }

    if (on_false) {
      ss << on_false->dump_gv();
    }

    ss << "\t\t" << get_gv_name();
    ss << " [shape=Mdiamond, label=\"";
    ss << pretty_print_expr(condition);
    ss << "\", color=yellow];\n";

    if (next) {
      ss << "\t\t" << get_gv_name();
      ss << " -> ";
      ss << next->get_gv_name();
      ss << " [label=\"True\"];\n";
    }

    if (on_false) {
      ss << "\t\t" << get_gv_name();
      ss << " -> ";
      ss << on_false->get_gv_name();
      ss << " [label=\"False\"];\n";
    }

    return ss.str();
  }
};

class ReturnRaw : public Node {
private:
  std::vector<calls_t> calls_list;

public:
  ReturnRaw(uint64_t _id, call_paths_t call_paths)
    : Node(_id, Node::NodeType::RETURN_RAW, nullptr, nullptr, call_paths.cp),
      calls_list(call_paths.backup) {}

  ReturnRaw(uint64_t _id, Node* _prev, std::vector<calls_t> _calls_list,
            const std::vector<std::string>& _call_paths_filenames,
            const std::vector<calls_t>& _missing_calls)
    : Node(_id, Node::NodeType::RETURN_RAW, nullptr, _prev, _call_paths_filenames, _missing_calls),
      calls_list(_calls_list) {}

  virtual Node* clone() const override {
    ReturnRaw* clone = new ReturnRaw(id, prev, calls_list, call_paths_filenames, missing_calls);
    return clone;
  }

  std::vector<calls_t> get_calls() const { return calls_list; }

  virtual void dump() const override {
    std::cerr << "===========================================" << "\n";
    std::cerr << "type:      return raw" << "\n";
    std::cerr << "lcalls:    " << calls_list.size() << "\n";
    for (const auto& calls : calls_list) {
      std::cerr << "calls:     " << calls.size() << "\n";
      for (const auto& call : calls) {
        std::cerr << "call:      " << call.function_name << " " << expr_to_string(call.ret) << "\n";
      }
    }

    std::cerr << "===========================================" << "\n";
  }

  virtual void dump_compact(int lvl) const override {
    assert(false);
  }

  virtual std::string dump_gv() const override {
    std::string ret;
    assert(false);
    return ret;
  }
};

class ReturnInit : public Node {
public:
  enum ReturnType {
    SUCCESS,
    FAILURE
  };

private:
  ReturnType value;

  void fill_return_value(calls_t calls) {
    assert(calls.size());

    auto start_time_finder = [](call_t call) -> bool {
      return call.function_name == "start_time";
    };

    auto start_time_it = std::find_if(calls.begin(), calls.end(), start_time_finder);
    auto found = (start_time_it != calls.end());

    value = found ? SUCCESS : FAILURE;
  }

protected:
  virtual std::string get_gv_name() const override {
    std::stringstream ss;

    ss << "\"return ";
    switch (value) {
    case SUCCESS: { ss << "1"; break; }
    case FAILURE: { ss << "0"; break; }
    default: { assert(false); }
    }
    ss << "\"";

    return ss.str();
  }

public:
  ReturnInit(uint64_t _id)
    : Node(_id, Node::NodeType::RETURN_INIT), value(SUCCESS) {}

  ReturnInit(uint64_t _id, const ReturnRaw* raw)
    : Node(_id, Node::NodeType::RETURN_INIT, nullptr, nullptr, raw->call_paths_filenames, raw->missing_calls) {
    auto calls_list = raw->get_calls();
    assert(calls_list.size());
    fill_return_value(calls_list[0]);
  }

  ReturnInit(uint64_t _id, Node *_prev, ReturnType _value)
    : Node(_id, Node::NodeType::RETURN_INIT, nullptr, _prev, _prev->call_paths_filenames, _prev->missing_calls),
      value(_value) {}

  ReturnType get_return_value() const {
    return value;
  }

  virtual Node* clone() const override {
    ReturnInit* clone = new ReturnInit(id, prev, value);
    return clone;
  }

  virtual void dump() const override {
    std::cerr << "===========================================" << "\n";
    std::cerr << "type:      return init" << "\n";
    std::cerr << "callpaths: ";
    int i = 0;
    for (const auto& filename : call_paths_filenames) {
      if (i > 0 && i % 5 == 0)  {
        std::cerr << "\n" << "           ";
      }
      if (i > 0 && i % 5 != 0) std::cerr << ", ";
      std::cerr << filename;
      i++;
    }
    std::cerr << "\n";
    std::cerr << "value:     ";
    switch (value) {
    case SUCCESS: { std::cerr << "SUCCESS"; break; }
    case FAILURE: { std::cerr << "FAILURE"; break; }
    default: { assert(false); }
    }
    std::cerr << "\n";
    std::cerr << "===========================================" << "\n";
  }

  virtual void dump_compact(int lvl) const override {
    std::string sep = std::string(lvl*2, ' ');
    std::cerr << sep;
    switch (value) {
    case SUCCESS: { std::cerr << "SUCCESS"; break; }
    case FAILURE: { std::cerr << "FAILURE"; break; }
    default: { assert(false); }
    }
    std::cerr << "\n";
  }

  virtual std::string dump_gv() const override {
    std::stringstream ss;

    ss << "\t\t\"return ";
    switch (value) {
    case SUCCESS: { ss << "1\" [color=chartreuse2]"; break; }
    case FAILURE: { ss << "0\" [color=brown1]"; break; }
    default: { assert(false); }
    }
    ss << ";\n";

    return ss.str();
  }
};

class ReturnProcess : public Node {
public:
  enum Operation { FWD, DROP, BCAST, ERR };

private:
  int value;
  Operation operation;

  std::pair<unsigned, unsigned> analyse_packet_sends(calls_t calls) const {
    unsigned counter = 0;
    unsigned dst_device = 0;

    for (const auto& call : calls) {
      if (call.function_name != "packet_send")
        continue;

      counter++;

      if (counter == 1) {
        auto dst_device_expr = call.args.at("dst_device").expr;
        assert(dst_device_expr->getKind() == klee::Expr::Kind::Constant);

        klee::ConstantExpr* dst_device_const = static_cast<klee::ConstantExpr*>(dst_device_expr.get());
        dst_device = dst_device_const->getZExtValue();
      }
    }

    return std::pair<unsigned, unsigned>(counter, dst_device);
  }

  void fill_return_value(calls_t calls) {
    auto counter_dst_device_pair = analyse_packet_sends(calls);

    if (counter_dst_device_pair.first == 1) {
      value = counter_dst_device_pair.second;
      operation = FWD;
      return;
    }

    if (counter_dst_device_pair.first > 1) {
      value = ((uint16_t) - 1);
      operation = BCAST;
      return;
    }

    auto packet_receive_finder = [](call_t call) -> bool {
      return call.function_name == "packet_receive";
    };

    auto packet_receive_it = std::find_if(calls.begin(), calls.end(), packet_receive_finder);

    if(packet_receive_it == calls.end()) {
      operation = ERR;
      value = -1;
      return;
    }

    auto packet_receive = *packet_receive_it;
    auto src_device_expr = packet_receive.args["src_devices"].expr;
    assert(src_device_expr->getKind() == klee::Expr::Kind::Constant);

    klee::ConstantExpr* src_device_const = static_cast<klee::ConstantExpr*>(src_device_expr.get());
    auto src_device = src_device_const->getZExtValue();

    operation = DROP;
    value = src_device;
    return;
  }

public:
  ReturnProcess(uint64_t _id, const ReturnRaw* raw)
    : Node(_id, Node::NodeType::RETURN_PROCESS, nullptr, nullptr, raw->call_paths_filenames, raw->missing_calls) {
    auto calls_list = raw->get_calls();
    assert(calls_list.size());
    fill_return_value(calls_list[0]);
  }

  ReturnProcess(uint64_t _id, Node *_prev, int _value, Operation _operation)
    : Node(_id, Node::NodeType::RETURN_PROCESS, nullptr, _prev, _prev->call_paths_filenames, _prev->missing_calls),
      value(_value), operation(_operation) {}

  int get_return_value() const {
    return value;
  }

  Operation get_return_operation() const {
    return operation;
  }

  virtual Node* clone() const override {
    ReturnProcess* clone = new ReturnProcess(id, prev, value, operation);
    return clone;
  }

  virtual void dump() const override {
    std::cerr << "===========================================" << "\n";
    std::cerr << "type:      return process" << "\n";
    std::cerr << "callpaths: ";
    int i = 0;
    for (const auto& filename : call_paths_filenames) {
      if (i > 0 && i % 5 == 0)  {
        std::cerr << "\n" << "           ";
      }
      if (i > 0 && i % 5 != 0) std::cerr << ", ";
      std::cerr << filename;
      i++;
    }
    std::cerr << "\n";
    std::cerr << "operation: ";
    switch (operation) {
    case FWD:   { std::cerr << "fwd(" << value << ")"; break; }
    case DROP:  { std::cerr << "drop()"; break; }
    case BCAST: { std::cerr << "bcast()"; break; }
    case ERR:   { std::cerr << "ERR"; break; }
    }
    std::cerr << "\n";
    std::cerr << "===========================================" << "\n";
  }

  virtual void dump_compact(int lvl) const override {
    std::string sep = std::string(lvl*2, ' ');
    std::cerr << sep;
    switch (operation) {
    case FWD:   { std::cerr << "fwd(" << value << ")"; break; }
    case DROP:  { std::cerr << "drop()"; break; }
    case BCAST: { std::cerr << "bcast()"; break; }
    case ERR:   { std::cerr << "ERR"; break; }
    }
    std::cerr << "\n";
  }

  virtual std::string dump_gv() const override {
    std::stringstream ss;

    ss << "\t\t" << get_gv_name();
    ss << " [label=\"";
    switch (operation) {
    case FWD:   { ss << "fwd(" << value << ")\", color=chartreuse2]"; break; }
    case DROP:  { ss << "drop()\", color=brown1]"; break; }
    case BCAST: { ss << "bcast()\", color=cyan]"; break; }
    default: { assert(false); }
    }
    ss << ";\n";

    return ss.str();
  }
};

class CallPathsGroup {
private:
  klee::ref<klee::Expr> discriminating_constraint;
  call_paths_t on_true;
  call_paths_t on_false;

  call_paths_t call_paths;
  solver_toolbox_t& solver_toolbox;

private:
  void group_call_paths();
  bool check_discriminating_constraint(klee::ref<klee::Expr> constraint);
  klee::ref<klee::Expr> find_discriminating_constraint();
  std::vector<klee::ref<klee::Expr>> get_possible_discriminating_constraints() const;
  bool satisfies_constraint(std::vector<call_path_t*> call_paths, klee::ref<klee::Expr> constraint) const;
  bool satisfies_constraint(call_path_t* call_path, klee::ref<klee::Expr> constraint) const;
  bool satisfies_not_constraint(std::vector<call_path_t*> call_paths, klee::ref<klee::Expr> constraint) const;
  bool satisfies_not_constraint(call_path_t* call_path, klee::ref<klee::Expr> constraint) const;
  bool are_calls_equal(call_t c1, call_t c2);
  call_t pop_call();

public:
  CallPathsGroup(const call_paths_t& _call_paths,
                 solver_toolbox_t& _solver_toolbox)
    : call_paths(_call_paths), solver_toolbox(_solver_toolbox) {
    group_call_paths();
  }

  klee::ref<klee::Expr> get_discriminating_constraint() const {
    return discriminating_constraint;
  }

  call_paths_t get_on_true() const {
    return on_true;
  }

  call_paths_t get_on_false() const {
    return on_false;
  }
};

class BDD {
protected:
  friend class CallPathsGroup;

private:
  solver_toolbox_t solver_toolbox;
  uint64_t id;

  std::shared_ptr<Node> nf_init;
  std::shared_ptr<Node> nf_process;

  static std::vector<std::string> skip_conditions_with_symbol;

  static constexpr char INIT_CONTEXT_MARKER[] = "start_time";

private:
  call_t get_successful_call(std::vector<call_path_t*> call_paths) const;
  Node* populate(call_paths_t call_paths);

  static std::string get_fname(const Node* node);
  static bool is_skip_function(const Node* node);
  static bool is_skip_condition(const Node* node);

  Node* populate_init(const Node* root);
  Node* populate_process(const Node* root, bool store=false);

  void add_node(call_t call);
  void dump(int lvl, const Node* node) const;

  uint64_t get_and_inc_id() { uint64_t _id = id; id++; return _id; }

public:
  BDD(std::vector<call_path_t*> call_paths) : id(0) {
    call_paths_t cp(call_paths);
    Node* root = populate(cp);

    nf_init = std::shared_ptr<Node>(populate_init(root));
    nf_process = std::shared_ptr<Node>(populate_process(root));

    delete root;
  }

  const Node* get_init()    const { return nf_init.get(); }
  const Node* get_process() const { return nf_process.get(); }

  const solver_toolbox_t& get_solver_toolbox() const { return solver_toolbox; }
  void dump() const;

  std::string dump_gv() const {
    std::stringstream ss;
    ss << "digraph mygraph {\n";
    ss << "\tnode [shape=box];\n";

    ss << "\tsubgraph clusterinit {\n";
    ss << "\t\tstyle=filled;\n";
    ss << "\t\tlabel=\"nf_init\";\n";
    ss << "\t\tnode [style=filled,color=white];\n";

    if (nf_init) ss << nf_init->dump_gv();
    ss << "\t}\n";

    ss << "\tsubgraph clusterprocess {\n";
    ss << "\t\tstyle=filled;\n";
    ss << "\t\tlabel=\"nf_process\"\n";
    ss << "\t\tnode [style=filled,color=white];\n";

    if (nf_process) ss << nf_process->dump_gv();
    ss << "\t}\n";

    ss << "}";

    return ss.str();
  }
};
}
