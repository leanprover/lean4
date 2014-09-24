add_library(numerics init_module.cpp mpz.cpp mpq.cpp mpbq.cpp mpfp.cpp
float.cpp double.cpp numeric_traits.cpp primes.cpp zpz.cpp)

target_link_libraries(numerics ${LEAN_LIBS} ${EXTRA_LIBS})
