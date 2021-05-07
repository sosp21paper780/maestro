#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_executable(load-call-paths
  main.cpp
  load-call-paths.cpp
)

set(KLEE_LIBS
  kleaverExpr
  kleeCore
)

target_link_libraries(load-call-paths ${KLEE_LIBS})

install(TARGETS load-call-paths RUNTIME DESTINATION bin)
