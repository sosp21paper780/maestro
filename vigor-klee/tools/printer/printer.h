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

std::string expr_to_string(klee::ref<klee::Expr> expr, bool one_liner=false);
std::string pretty_print_expr(klee::ref<klee::Expr> expr);

class RetrieveSymbols : public klee::ExprVisitor::ExprVisitor {
private:
  std::vector<klee::ref<klee::ReadExpr>> retrieved;
  std::vector<std::string> retrieved_strings;

public:
  RetrieveSymbols() : ExprVisitor(true) {}

  klee::ExprVisitor::Action visitRead(const klee::ReadExpr &e) {
    klee::UpdateList ul = e.updates;
    const klee::Array *root = ul.root;

    auto found_it = std::find(retrieved_strings.begin(), retrieved_strings.end(), root->name);
    if (found_it == retrieved_strings.end()) {
      retrieved_strings.push_back(root->name);
    }

    retrieved.emplace_back((const_cast<klee::ReadExpr *>(&e)));
    return klee::ExprVisitor::Action::doChildren();
  }

  std::vector<klee::ref<klee::ReadExpr>> get_retrieved() {
    return retrieved;
  }

  std::vector<std::string> get_retrieved_strings() {
    return retrieved_strings;
  }

  static bool contains(klee::ref<klee::Expr> expr, const std::string& symbol) {
    RetrieveSymbols retriever;
    retriever.visit(expr);
    auto symbols = retriever.get_retrieved_strings();
    auto found_it = std::find(symbols.begin(), symbols.end(), symbol);
    return found_it != symbols.end();
  }
};
