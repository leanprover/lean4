include_directories (${LEAN_SOURCE_DIR}/util) 
add_library(numerics gmp_init.cpp mpz.cpp mpq.cpp mpbq.cpp)
