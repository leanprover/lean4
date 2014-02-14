add_library(kernel level.cpp diff_cnstrs.cpp
# expr.cpp
# free_vars.cpp abstract.cpp instantiate.cpp
# normalizer.cpp context.cpp level.cpp object.cpp environment.cpp
# type_checker.cpp kernel.cpp occurs.cpp metavar.cpp
# justification.cpp unification_constraint.cpp kernel_exception.cpp
# type_checker_justification.cpp pos_info_provider.cpp
# replace_visitor.cpp update_expr.cpp io_state.cpp max_sharing.cpp
# universe_constraints.cpp
)

target_link_libraries(kernel ${LEAN_LIBS})
