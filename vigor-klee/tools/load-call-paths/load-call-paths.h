#pragma once

#include "klee/ExprBuilder.h"
#include "klee/Constraints.h"

typedef struct {
  klee::ref<klee::Expr> expr;
  std::pair<bool, std::string> fn_ptr_name;
  klee::ref<klee::Expr> in;
  klee::ref<klee::Expr> out;
} arg_t;

typedef struct {
  std::string function_name;
  std::map<std::string, std::pair<klee::ref<klee::Expr>,
                                  klee::ref<klee::Expr> > > extra_vars;
  std::map<std::string, arg_t> args;

  klee::ref<klee::Expr> ret;
} call_t;

typedef std::vector<call_t> calls_t;

typedef struct call_path {
  std::string file_name;
  klee::ConstraintManager constraints;
  calls_t calls;
  std::map<std::string, const klee::Array *> arrays;
} call_path_t;

call_path_t *load_call_path(std::string file_name,
                            std::vector<std::string> expressions_str,
                            std::deque<klee::ref<klee::Expr> > &expressions);


inline std::ostream& operator<<(std::ostream& str, const call_path_t& cp) {
  str << "  Calls:" << "\n";
  for (auto call : cp.calls) {
    str << "    Function: " << call.function_name << "\n";
    if (!call.args.empty()) {
      str << "      With Args:" << "\n";
      for (auto arg : call.args) {
        str << "        " << arg.first << "\n";

        str << "            Expr: ";
        arg.second.expr->dump();

        if (!arg.second.in.isNull()) {
          str << "            Before: ";
          arg.second.in->dump();
        }

        if (!arg.second.out.isNull()) {
          str << "            After: ";
          arg.second.out->dump();
        }

        if (arg.second.fn_ptr_name.first) {
          str << "            Fn: " << arg.second.fn_ptr_name.second;
          str << "\n";
        }
      }
    }
    if (!call.extra_vars.empty()) {
      str << "      With Extra Vars:" << "\n";
      for (auto extra_var : call.extra_vars) {
        str << "        " << extra_var.first << "\n";
        if (!extra_var.second.first.isNull()) {
          str << "            Before: ";
          extra_var.second.first->dump();
        }
        if (!extra_var.second.second.isNull()) {
          str << "            After: ";
          extra_var.second.second->dump();
        }
      }
    }

    if (!call.ret.isNull()) {
      str << "      With Ret: ";
      call.ret->dump();
    }
  }

  return str;
}
