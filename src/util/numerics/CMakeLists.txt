add_library(numerics gmp_init.cpp mpz.cpp mpq.cpp mpbq.cpp mpfp.cpp
float.cpp double.cpp numeric_traits.cpp primes.cpp zpz.cpp)

target_link_libraries(numerics ${LEAN_LIBS} ${EXTRA_LIBS})
