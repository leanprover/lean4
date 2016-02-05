string(TOLOWER "${CMAKE_BUILD_TYPE}" CMAKE_BUILD_TYPE_lower)
if (CMAKE_BUILD_TYPE_lower STREQUAL "debug")
  # LP_DBG_FILES include files that are only needed in DEBUG mode.
  # We use this trick to avoid warning messages when compiling in Release mode on OSX.
  # These files are empty in Release mode.
  set(LP_DBG_FILES dense_matrix_instances.cpp matrix_instances.cpp)
endif()

add_library(lp OBJECT
  binary_heap_priority_queue_instances.cpp
  binary_heap_upair_queue_instances.cpp
  core_solver_pretty_printer_instances.cpp
  indexed_vector_instances.cpp
  lar_core_solver_instances.cpp
  lar_solver_instances.cpp
  lp_core_solver_base_instances.cpp
  lp_dual_core_solver_instances.cpp
  lp_dual_simplex_instances.cpp
  lp_primal_core_solver_instances.cpp
  lp_primal_simplex_instances.cpp
  lp_settings_instances.cpp
  lp_solver_instances.cpp
  lu_instances.cpp
  permutation_matrix_instances.cpp
  row_eta_matrix_instances.cpp
  sparse_matrix_instances.cpp
  square_dense_submatrix_instances.cpp
  static_matrix_instances.cpp
  scaler_instances.cpp
  eta_matrix_instances.cpp
  lar_constraints.cpp
  ${LP_DBG_FILES}
  )
