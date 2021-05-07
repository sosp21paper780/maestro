#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_executable(analyse-libvig-call-paths
  analyse-libvig-call-paths.cpp
  ../load-call-paths/load-call-paths.cpp
)

set(KLEE_LIBS
  kleaverExpr
  kleeCore
)

target_include_directories(analyse-libvig-call-paths PRIVATE ../load-call-paths)
target_link_libraries(analyse-libvig-call-paths ${KLEE_LIBS})

install(TARGETS analyse-libvig-call-paths RUNTIME DESTINATION bin)
