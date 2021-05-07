#include "call-paths-to-bdd.h"

namespace {
llvm::cl::list<std::string> InputCallPathFiles(llvm::cl::desc("<call paths>"),
                                               llvm::cl::Positional,
                                               llvm::cl::OneOrMore);


llvm::cl::OptionCategory BDDGeneratorCat("BDD generator specific options");

llvm::cl::opt<std::string> Gv(
    "gv",
    llvm::cl::desc("GraphViz file for BDD visualization."),
    llvm::cl::cat(BDDGeneratorCat));
}

int main(int argc, char **argv) {
  llvm::cl::ParseCommandLineOptions(argc, argv);
  std::vector<call_path_t*> call_paths;

  for (auto file : InputCallPathFiles) {
    std::cerr << "Loading: " << file << std::endl;

    std::vector<std::string> expressions_str;
    std::deque<klee::ref<klee::Expr>> expressions;

    call_path_t *call_path = load_call_path(file, expressions_str, expressions);
    call_paths.push_back(call_path);
  }

  BDD::BDD bdd(call_paths);

  bdd.dump();
  for (auto call_path : call_paths) {
    delete call_path;
  }

  if (Gv.size()) {
    auto file = std::ofstream(Gv);
    assert(file.is_open());
    file << bdd.dump_gv();
  }

  return 0;
}
