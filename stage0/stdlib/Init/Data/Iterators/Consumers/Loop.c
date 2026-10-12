// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Loop
// Imports: public import Init.Data.Iterators.Consumers.Monadic.Loop public import Init.Data.Iterators.Consumers.Partial public import Init.Data.Iterators.Consumers.Total
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Iter_instForIn_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Iter_instForIn_x27___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Iter_instForIn_x27___redArg___closed__0 = (const lean_object*)&l_Std_Iter_instForIn_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInIterOfMonadOfIteratorLoopId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInIterOfMonadOfIteratorLoopId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInIterOfMonadOfIteratorLoopId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_instForIn_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_instForIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_instForIn_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInPartialOfMonadOfIteratorLoopId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInPartialOfMonadOfIteratorLoopId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInPartialOfMonadOfIteratorLoopId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_instForIn_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_instForIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_instForIn_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMPartialOfIteratorLoopIdOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMPartialOfIteratorLoopIdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMPartialOfIteratorLoopIdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_foldM___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_foldM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Iter_foldM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Iter_foldM___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Iter_foldM___redArg___closed__0 = (const lean_object*)&l_Std_Iter_foldM___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Iter_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_fold___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__0(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_anyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_anyM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_anyM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_anyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_anyM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_any___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Iter_any___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Iter_any___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_any___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Iter_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Iter_Total_any___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_any___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Iter_Total_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg___lam__2(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_allM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_allM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_allM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_allM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_allM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_all___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Iter_all___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Iter_all___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_all___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Iter_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Iter_Total_all___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_all___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Iter_Total_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSome_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSome_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Iter_first_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Iter_first_x3f___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Iter_first_x3f___redArg___closed__0 = (const lean_object*)&l_Std_Iter_first_x3f___redArg___closed__0_value;
static const lean_closure_object l_Std_Iter_first_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Iter_first_x3f___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Iter_first_x3f___redArg___closed__1 = (const lean_object*)&l_Std_Iter_first_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_first_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_first_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_first_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Iter_isEmpty___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Iter_isEmpty___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_Iter_isEmpty___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Iter_isEmpty___redArg___lam__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Iter_isEmpty___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Iter_isEmpty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Iter_isEmpty___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Iter_isEmpty___redArg___closed__0 = (const lean_object*)&l_Std_Iter_isEmpty___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Iter_isEmpty___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_isEmpty___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Iter_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Iter_Total_isEmpty___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_isEmpty___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Iter_Total_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_length___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_length___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_length___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Iter_length___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Iter_length___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Iter_length___redArg___closed__0 = (const lean_object*)&l_Std_Iter_length___redArg___closed__0_value;
static const lean_closure_object l_Std_Iter_length___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Iter_length___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Iter_length___redArg___closed__1 = (const lean_object*)&l_Std_Iter_length___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Iter_length___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_length(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_length___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg___lam__0(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_f_3_, lean_object* v_c_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_apply_1(v_f_3_, v_c_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg___lam__1(lean_object* v_toPure_6_, lean_object* v_____do__lift_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_apply_2(v_toPure_6_, lean_box(0), v_____do__lift_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg___lam__2(lean_object* v_f_9_, lean_object* v_toBind_10_, lean_object* v___f_11_, lean_object* v_x1_12_, lean_object* v_x2_13_, lean_object* v_x3_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_apply_3(v_f_9_, v_x1_12_, lean_box(0), v_x3_14_);
v___x_16_ = lean_apply_4(v_toBind_10_, lean_box(0), lean_box(0), v___x_15_, v___f_11_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg___lam__3(lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v___f_19_, lean_object* v_00_u03b2_20_, lean_object* v_it_21_, lean_object* v_init_22_, lean_object* v_f_23_){
_start:
{
lean_object* v_toApplicative_24_; lean_object* v_toBind_25_; lean_object* v_toPure_26_; lean_object* v___f_27_; lean_object* v___f_28_; lean_object* v___x_29_; 
v_toApplicative_24_ = lean_ctor_get(v_inst_17_, 0);
lean_inc_ref(v_toApplicative_24_);
v_toBind_25_ = lean_ctor_get(v_inst_17_, 1);
lean_inc(v_toBind_25_);
lean_dec_ref(v_inst_17_);
v_toPure_26_ = lean_ctor_get(v_toApplicative_24_, 1);
lean_inc(v_toPure_26_);
lean_dec_ref(v_toApplicative_24_);
v___f_27_ = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__1), 2, 1);
lean_closure_set(v___f_27_, 0, v_toPure_26_);
v___f_28_ = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__2), 6, 3);
lean_closure_set(v___f_28_, 0, v_f_23_);
lean_closure_set(v___f_28_, 1, v_toBind_25_);
lean_closure_set(v___f_28_, 2, v___f_27_);
v___x_29_ = lean_apply_6(v_inst_18_, v___f_19_, lean_box(0), lean_box(0), v_it_21_, v_init_22_, v___f_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg(lean_object* v_inst_31_, lean_object* v_inst_32_){
_start:
{
lean_object* v___f_33_; lean_object* v___f_34_; 
v___f_33_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_34_ = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__3), 7, 3);
lean_closure_set(v___f_34_, 0, v_inst_31_);
lean_closure_set(v___f_34_, 1, v_inst_32_);
lean_closure_set(v___f_34_, 2, v___f_33_);
return v___f_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27(lean_object* v_00_u03b1_35_, lean_object* v_00_u03b2_36_, lean_object* v_n_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_){
_start:
{
lean_object* v___f_41_; lean_object* v___f_42_; 
v___f_41_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_42_ = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__3), 7, 3);
lean_closure_set(v___f_42_, 0, v_inst_38_);
lean_closure_set(v___f_42_, 1, v_inst_40_);
lean_closure_set(v___f_42_, 2, v___f_41_);
return v___f_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___boxed(lean_object* v_00_u03b1_43_, lean_object* v_00_u03b2_44_, lean_object* v_n_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_inst_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Std_Iter_instForIn_x27(v_00_u03b1_43_, v_00_u03b2_44_, v_n_45_, v_inst_46_, v_inst_47_, v_inst_48_);
lean_dec(v_inst_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInIterOfMonadOfIteratorLoopId___redArg(lean_object* v_inst_50_, lean_object* v_inst_51_){
_start:
{
lean_object* v___f_52_; lean_object* v___f_53_; lean_object* v___f_54_; 
v___f_52_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_53_ = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__3), 7, 3);
lean_closure_set(v___f_53_, 0, v_inst_50_);
lean_closure_set(v___f_53_, 1, v_inst_51_);
lean_closure_set(v___f_53_, 2, v___f_52_);
v___f_54_ = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(v___f_54_, 0, v___f_53_);
return v___f_54_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInIterOfMonadOfIteratorLoopId(lean_object* v_00_u03b1_55_, lean_object* v_00_u03b2_56_, lean_object* v_n_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Std_instForInIterOfMonadOfIteratorLoopId___redArg(v_inst_58_, v_inst_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInIterOfMonadOfIteratorLoopId___boxed(lean_object* v_00_u03b1_62_, lean_object* v_00_u03b2_63_, lean_object* v_n_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_inst_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Std_instForInIterOfMonadOfIteratorLoopId(v_00_u03b1_62_, v_00_u03b2_63_, v_n_64_, v_inst_65_, v_inst_66_, v_inst_67_);
lean_dec(v_inst_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_instForIn_x27___redArg(lean_object* v_inst_69_, lean_object* v_inst_70_){
_start:
{
lean_object* v___f_71_; lean_object* v___f_72_; 
v___f_71_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_72_ = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__3), 7, 3);
lean_closure_set(v___f_72_, 0, v_inst_69_);
lean_closure_set(v___f_72_, 1, v_inst_70_);
lean_closure_set(v___f_72_, 2, v___f_71_);
return v___f_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_instForIn_x27(lean_object* v_00_u03b1_73_, lean_object* v_00_u03b2_74_, lean_object* v_n_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_inst_78_){
_start:
{
lean_object* v___f_79_; lean_object* v___f_80_; 
v___f_79_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_80_ = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__3), 7, 3);
lean_closure_set(v___f_80_, 0, v_inst_76_);
lean_closure_set(v___f_80_, 1, v_inst_78_);
lean_closure_set(v___f_80_, 2, v___f_79_);
return v___f_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_instForIn_x27___boxed(lean_object* v_00_u03b1_81_, lean_object* v_00_u03b2_82_, lean_object* v_n_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_inst_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Std_Iter_Partial_instForIn_x27(v_00_u03b1_81_, v_00_u03b2_82_, v_n_83_, v_inst_84_, v_inst_85_, v_inst_86_);
lean_dec(v_inst_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInPartialOfMonadOfIteratorLoopId___redArg(lean_object* v_inst_88_, lean_object* v_inst_89_){
_start:
{
lean_object* v___f_90_; lean_object* v___f_91_; lean_object* v___f_92_; 
v___f_90_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_91_ = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__3), 7, 3);
lean_closure_set(v___f_91_, 0, v_inst_88_);
lean_closure_set(v___f_91_, 1, v_inst_89_);
lean_closure_set(v___f_91_, 2, v___f_90_);
v___f_92_ = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(v___f_92_, 0, v___f_91_);
return v___f_92_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInPartialOfMonadOfIteratorLoopId(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_n_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_inst_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Std_instForInPartialOfMonadOfIteratorLoopId___redArg(v_inst_96_, v_inst_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInPartialOfMonadOfIteratorLoopId___boxed(lean_object* v_00_u03b1_100_, lean_object* v_00_u03b2_101_, lean_object* v_n_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_inst_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Std_instForInPartialOfMonadOfIteratorLoopId(v_00_u03b1_100_, v_00_u03b2_101_, v_n_102_, v_inst_103_, v_inst_104_, v_inst_105_);
lean_dec(v_inst_104_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_instForIn_x27___redArg(lean_object* v_inst_107_, lean_object* v_inst_108_){
_start:
{
lean_object* v___f_109_; lean_object* v___f_110_; 
v___f_109_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_110_ = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__3), 7, 3);
lean_closure_set(v___f_110_, 0, v_inst_107_);
lean_closure_set(v___f_110_, 1, v_inst_108_);
lean_closure_set(v___f_110_, 2, v___f_109_);
return v___f_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_instForIn_x27(lean_object* v_00_u03b1_111_, lean_object* v_00_u03b2_112_, lean_object* v_n_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_inst_117_){
_start:
{
lean_object* v___f_118_; lean_object* v___f_119_; 
v___f_118_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_119_ = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__3), 7, 3);
lean_closure_set(v___f_119_, 0, v_inst_114_);
lean_closure_set(v___f_119_, 1, v_inst_116_);
lean_closure_set(v___f_119_, 2, v___f_118_);
return v___f_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_instForIn_x27___boxed(lean_object* v_00_u03b1_120_, lean_object* v_00_u03b2_121_, lean_object* v_n_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_inst_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Std_Iter_Total_instForIn_x27(v_00_u03b1_120_, v_00_u03b2_121_, v_n_122_, v_inst_123_, v_inst_124_, v_inst_125_, v_inst_126_);
lean_dec(v_inst_124_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId___redArg(lean_object* v_inst_128_, lean_object* v_inst_129_){
_start:
{
lean_object* v___f_130_; lean_object* v___f_131_; lean_object* v___f_132_; 
v___f_130_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_131_ = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__3), 7, 3);
lean_closure_set(v___f_131_, 0, v_inst_128_);
lean_closure_set(v___f_131_, 1, v_inst_129_);
lean_closure_set(v___f_131_, 2, v___f_130_);
v___f_132_ = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(v___f_132_, 0, v___f_131_);
return v___f_132_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId(lean_object* v_00_u03b1_133_, lean_object* v_00_u03b2_134_, lean_object* v_n_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_inst_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId___redArg(v_inst_136_, v_inst_138_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId___boxed(lean_object* v_00_u03b1_141_, lean_object* v_00_u03b2_142_, lean_object* v_n_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_inst_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId(v_00_u03b1_141_, v_00_u03b2_142_, v_n_143_, v_inst_144_, v_inst_145_, v_inst_146_, v_inst_147_);
lean_dec(v_inst_145_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__1(lean_object* v_toPure_149_, lean_object* v_____do__lift_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_apply_2(v_toPure_149_, lean_box(0), v_____do__lift_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__0(lean_object* v___x_152_, lean_object* v_toPure_153_, lean_object* v_____r_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_152_);
v___x_156_ = lean_apply_2(v_toPure_153_, lean_box(0), v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__2(lean_object* v_f_157_, lean_object* v_toBind_158_, lean_object* v___f_159_, lean_object* v___f_160_, lean_object* v_x1_161_, lean_object* v_x2_162_, lean_object* v_x3_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_apply_1(v_f_157_, v_x1_161_);
lean_inc(v_toBind_158_);
v___x_165_ = lean_apply_4(v_toBind_158_, lean_box(0), lean_box(0), v___x_164_, v___f_159_);
v___x_166_ = lean_apply_4(v_toBind_158_, lean_box(0), lean_box(0), v___x_165_, v___f_160_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__3(lean_object* v_toPure_167_, lean_object* v_toBind_168_, lean_object* v___f_169_, lean_object* v_inst_170_, lean_object* v___f_171_, lean_object* v_it_172_, lean_object* v_f_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___x_177_; 
v___x_174_ = lean_box(0);
v___f_175_ = lean_alloc_closure((void*)(l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_175_, 0, v___x_174_);
lean_closure_set(v___f_175_, 1, v_toPure_167_);
v___f_176_ = lean_alloc_closure((void*)(l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__2), 7, 4);
lean_closure_set(v___f_176_, 0, v_f_173_);
lean_closure_set(v___f_176_, 1, v_toBind_168_);
lean_closure_set(v___f_176_, 2, v___f_175_);
lean_closure_set(v___f_176_, 3, v___f_169_);
v___x_177_ = lean_apply_6(v_inst_170_, v___f_171_, lean_box(0), lean_box(0), v_it_172_, v___x_174_, v___f_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg(lean_object* v_inst_178_, lean_object* v_inst_179_){
_start:
{
lean_object* v_toApplicative_180_; lean_object* v_toBind_181_; lean_object* v_toPure_182_; lean_object* v___f_183_; lean_object* v___f_184_; lean_object* v___f_185_; 
v_toApplicative_180_ = lean_ctor_get(v_inst_179_, 0);
lean_inc_ref(v_toApplicative_180_);
v_toBind_181_ = lean_ctor_get(v_inst_179_, 1);
lean_inc(v_toBind_181_);
lean_dec_ref(v_inst_179_);
v_toPure_182_ = lean_ctor_get(v_toApplicative_180_, 1);
lean_inc_n(v_toPure_182_, 2);
lean_dec_ref(v_toApplicative_180_);
v___f_183_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_184_ = lean_alloc_closure((void*)(l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_184_, 0, v_toPure_182_);
v___f_185_ = lean_alloc_closure((void*)(l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__3), 7, 5);
lean_closure_set(v___f_185_, 0, v_toPure_182_);
lean_closure_set(v___f_185_, 1, v_toBind_181_);
lean_closure_set(v___f_185_, 2, v___f_184_);
lean_closure_set(v___f_185_, 3, v_inst_178_);
lean_closure_set(v___f_185_, 4, v___f_183_);
return v___f_185_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad(lean_object* v_m_186_, lean_object* v_00_u03b1_187_, lean_object* v_00_u03b2_188_, lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_inst_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg(v_inst_190_, v_inst_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___boxed(lean_object* v_m_193_, lean_object* v_00_u03b1_194_, lean_object* v_00_u03b2_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_inst_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_instForMIterOfIteratorLoopIdOfMonad(v_m_193_, v_00_u03b1_194_, v_00_u03b2_195_, v_inst_196_, v_inst_197_, v_inst_198_);
lean_dec(v_inst_196_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMPartialOfIteratorLoopIdOfMonad___redArg(lean_object* v_inst_200_, lean_object* v_inst_201_){
_start:
{
lean_object* v_toApplicative_202_; lean_object* v_toBind_203_; lean_object* v_toPure_204_; lean_object* v___f_205_; lean_object* v___f_206_; lean_object* v___f_207_; 
v_toApplicative_202_ = lean_ctor_get(v_inst_201_, 0);
lean_inc_ref(v_toApplicative_202_);
v_toBind_203_ = lean_ctor_get(v_inst_201_, 1);
lean_inc(v_toBind_203_);
lean_dec_ref(v_inst_201_);
v_toPure_204_ = lean_ctor_get(v_toApplicative_202_, 1);
lean_inc_n(v_toPure_204_, 2);
lean_dec_ref(v_toApplicative_202_);
v___f_205_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_206_ = lean_alloc_closure((void*)(l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_206_, 0, v_toPure_204_);
v___f_207_ = lean_alloc_closure((void*)(l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__3), 7, 5);
lean_closure_set(v___f_207_, 0, v_toPure_204_);
lean_closure_set(v___f_207_, 1, v_toBind_203_);
lean_closure_set(v___f_207_, 2, v___f_206_);
lean_closure_set(v___f_207_, 3, v_inst_200_);
lean_closure_set(v___f_207_, 4, v___f_205_);
return v___f_207_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMPartialOfIteratorLoopIdOfMonad(lean_object* v_m_208_, lean_object* v_00_u03b1_209_, lean_object* v_00_u03b2_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_inst_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Std_instForMPartialOfIteratorLoopIdOfMonad___redArg(v_inst_212_, v_inst_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMPartialOfIteratorLoopIdOfMonad___boxed(lean_object* v_m_215_, lean_object* v_00_u03b1_216_, lean_object* v_00_u03b2_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_inst_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Std_instForMPartialOfIteratorLoopIdOfMonad(v_m_215_, v_00_u03b1_216_, v_00_u03b2_217_, v_inst_218_, v_inst_219_, v_inst_220_);
lean_dec(v_inst_218_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId___redArg(lean_object* v_inst_222_, lean_object* v_inst_223_){
_start:
{
lean_object* v_toApplicative_224_; lean_object* v_toBind_225_; lean_object* v_toPure_226_; lean_object* v___f_227_; lean_object* v___f_228_; lean_object* v___f_229_; 
v_toApplicative_224_ = lean_ctor_get(v_inst_222_, 0);
lean_inc_ref(v_toApplicative_224_);
v_toBind_225_ = lean_ctor_get(v_inst_222_, 1);
lean_inc(v_toBind_225_);
lean_dec_ref(v_inst_222_);
v_toPure_226_ = lean_ctor_get(v_toApplicative_224_, 1);
lean_inc_n(v_toPure_226_, 2);
lean_dec_ref(v_toApplicative_224_);
v___f_227_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_228_ = lean_alloc_closure((void*)(l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_228_, 0, v_toPure_226_);
v___f_229_ = lean_alloc_closure((void*)(l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__3), 7, 5);
lean_closure_set(v___f_229_, 0, v_toPure_226_);
lean_closure_set(v___f_229_, 1, v_toBind_225_);
lean_closure_set(v___f_229_, 2, v___f_228_);
lean_closure_set(v___f_229_, 3, v_inst_223_);
lean_closure_set(v___f_229_, 4, v___f_227_);
return v___f_229_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId(lean_object* v_m_230_, lean_object* v_00_u03b1_231_, lean_object* v_00_u03b2_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_inst_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId___redArg(v_inst_233_, v_inst_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId___boxed(lean_object* v_m_238_, lean_object* v_00_u03b1_239_, lean_object* v_00_u03b2_240_, lean_object* v_inst_241_, lean_object* v_inst_242_, lean_object* v_inst_243_, lean_object* v_inst_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId(v_m_238_, v_00_u03b1_239_, v_00_u03b2_240_, v_inst_241_, v_inst_242_, v_inst_243_, v_inst_244_);
lean_dec(v_inst_242_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_foldM___redArg___lam__1(lean_object* v_a_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_247_, 0, v_a_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_foldM___redArg___lam__2(lean_object* v_toFunctor_248_, lean_object* v_f_249_, lean_object* v___f_250_, lean_object* v_toBind_251_, lean_object* v___f_252_, lean_object* v_x1_253_, lean_object* v_x2_254_, lean_object* v_x3_255_){
_start:
{
lean_object* v_map_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_map_256_ = lean_ctor_get(v_toFunctor_248_, 0);
lean_inc(v_map_256_);
lean_dec_ref(v_toFunctor_248_);
v___x_257_ = lean_apply_2(v_f_249_, v_x3_255_, v_x1_253_);
v___x_258_ = lean_apply_4(v_map_256_, lean_box(0), lean_box(0), v___f_250_, v___x_257_);
v___x_259_ = lean_apply_4(v_toBind_251_, lean_box(0), lean_box(0), v___x_258_, v___f_252_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_foldM___redArg(lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_f_263_, lean_object* v_init_264_, lean_object* v_it_265_){
_start:
{
lean_object* v_toApplicative_266_; lean_object* v_toBind_267_; lean_object* v_toFunctor_268_; lean_object* v_toPure_269_; lean_object* v___f_270_; lean_object* v___f_271_; lean_object* v___f_272_; lean_object* v___f_273_; lean_object* v___x_274_; 
v_toApplicative_266_ = lean_ctor_get(v_inst_261_, 0);
lean_inc_ref(v_toApplicative_266_);
v_toBind_267_ = lean_ctor_get(v_inst_261_, 1);
lean_inc(v_toBind_267_);
lean_dec_ref(v_inst_261_);
v_toFunctor_268_ = lean_ctor_get(v_toApplicative_266_, 0);
lean_inc_ref(v_toFunctor_268_);
v_toPure_269_ = lean_ctor_get(v_toApplicative_266_, 1);
lean_inc(v_toPure_269_);
lean_dec_ref(v_toApplicative_266_);
v___f_270_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_271_ = ((lean_object*)(l_Std_Iter_foldM___redArg___closed__0));
v___f_272_ = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__1), 2, 1);
lean_closure_set(v___f_272_, 0, v_toPure_269_);
v___f_273_ = lean_alloc_closure((void*)(l_Std_Iter_foldM___redArg___lam__2), 8, 5);
lean_closure_set(v___f_273_, 0, v_toFunctor_268_);
lean_closure_set(v___f_273_, 1, v_f_263_);
lean_closure_set(v___f_273_, 2, v___f_271_);
lean_closure_set(v___f_273_, 3, v_toBind_267_);
lean_closure_set(v___f_273_, 4, v___f_272_);
v___x_274_ = lean_apply_6(v_inst_262_, v___f_270_, lean_box(0), lean_box(0), v_it_265_, v_init_264_, v___f_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_foldM(lean_object* v_m_275_, lean_object* v_inst_276_, lean_object* v_00_u03b1_277_, lean_object* v_00_u03b2_278_, lean_object* v_00_u03b3_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_f_282_, lean_object* v_init_283_, lean_object* v_it_284_){
_start:
{
lean_object* v_toApplicative_285_; lean_object* v_toBind_286_; lean_object* v_toFunctor_287_; lean_object* v_toPure_288_; lean_object* v___f_289_; lean_object* v___f_290_; lean_object* v___f_291_; lean_object* v___f_292_; lean_object* v___x_293_; 
v_toApplicative_285_ = lean_ctor_get(v_inst_276_, 0);
lean_inc_ref(v_toApplicative_285_);
v_toBind_286_ = lean_ctor_get(v_inst_276_, 1);
lean_inc(v_toBind_286_);
lean_dec_ref(v_inst_276_);
v_toFunctor_287_ = lean_ctor_get(v_toApplicative_285_, 0);
lean_inc_ref(v_toFunctor_287_);
v_toPure_288_ = lean_ctor_get(v_toApplicative_285_, 1);
lean_inc(v_toPure_288_);
lean_dec_ref(v_toApplicative_285_);
v___f_289_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_290_ = ((lean_object*)(l_Std_Iter_foldM___redArg___closed__0));
v___f_291_ = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__1), 2, 1);
lean_closure_set(v___f_291_, 0, v_toPure_288_);
v___f_292_ = lean_alloc_closure((void*)(l_Std_Iter_foldM___redArg___lam__2), 8, 5);
lean_closure_set(v___f_292_, 0, v_toFunctor_287_);
lean_closure_set(v___f_292_, 1, v_f_282_);
lean_closure_set(v___f_292_, 2, v___f_290_);
lean_closure_set(v___f_292_, 3, v_toBind_286_);
lean_closure_set(v___f_292_, 4, v___f_291_);
v___x_293_ = lean_apply_6(v_inst_281_, v___f_289_, lean_box(0), lean_box(0), v_it_284_, v_init_283_, v___f_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_foldM___boxed(lean_object* v_m_294_, lean_object* v_inst_295_, lean_object* v_00_u03b1_296_, lean_object* v_00_u03b2_297_, lean_object* v_00_u03b3_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_f_301_, lean_object* v_init_302_, lean_object* v_it_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Std_Iter_foldM(v_m_294_, v_inst_295_, v_00_u03b1_296_, v_00_u03b2_297_, v_00_u03b3_298_, v_inst_299_, v_inst_300_, v_f_301_, v_init_302_, v_it_303_);
lean_dec(v_inst_299_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_foldM___redArg(lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_f_307_, lean_object* v_init_308_, lean_object* v_it_309_){
_start:
{
lean_object* v_toApplicative_310_; lean_object* v_toBind_311_; lean_object* v_toFunctor_312_; lean_object* v_toPure_313_; lean_object* v___f_314_; lean_object* v___f_315_; lean_object* v___f_316_; lean_object* v___f_317_; lean_object* v___x_318_; 
v_toApplicative_310_ = lean_ctor_get(v_inst_305_, 0);
lean_inc_ref(v_toApplicative_310_);
v_toBind_311_ = lean_ctor_get(v_inst_305_, 1);
lean_inc(v_toBind_311_);
lean_dec_ref(v_inst_305_);
v_toFunctor_312_ = lean_ctor_get(v_toApplicative_310_, 0);
lean_inc_ref(v_toFunctor_312_);
v_toPure_313_ = lean_ctor_get(v_toApplicative_310_, 1);
lean_inc(v_toPure_313_);
lean_dec_ref(v_toApplicative_310_);
v___f_314_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_315_ = ((lean_object*)(l_Std_Iter_foldM___redArg___closed__0));
v___f_316_ = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__1), 2, 1);
lean_closure_set(v___f_316_, 0, v_toPure_313_);
v___f_317_ = lean_alloc_closure((void*)(l_Std_Iter_foldM___redArg___lam__2), 8, 5);
lean_closure_set(v___f_317_, 0, v_toFunctor_312_);
lean_closure_set(v___f_317_, 1, v_f_307_);
lean_closure_set(v___f_317_, 2, v___f_315_);
lean_closure_set(v___f_317_, 3, v_toBind_311_);
lean_closure_set(v___f_317_, 4, v___f_316_);
v___x_318_ = lean_apply_6(v_inst_306_, v___f_314_, lean_box(0), lean_box(0), v_it_309_, v_init_308_, v___f_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_foldM(lean_object* v_m_319_, lean_object* v_inst_320_, lean_object* v_00_u03b1_321_, lean_object* v_00_u03b2_322_, lean_object* v_00_u03b3_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_f_327_, lean_object* v_init_328_, lean_object* v_it_329_){
_start:
{
lean_object* v_toApplicative_330_; lean_object* v_toBind_331_; lean_object* v_toFunctor_332_; lean_object* v_toPure_333_; lean_object* v___f_334_; lean_object* v___f_335_; lean_object* v___f_336_; lean_object* v___f_337_; lean_object* v___x_338_; 
v_toApplicative_330_ = lean_ctor_get(v_inst_320_, 0);
lean_inc_ref(v_toApplicative_330_);
v_toBind_331_ = lean_ctor_get(v_inst_320_, 1);
lean_inc(v_toBind_331_);
lean_dec_ref(v_inst_320_);
v_toFunctor_332_ = lean_ctor_get(v_toApplicative_330_, 0);
lean_inc_ref(v_toFunctor_332_);
v_toPure_333_ = lean_ctor_get(v_toApplicative_330_, 1);
lean_inc(v_toPure_333_);
lean_dec_ref(v_toApplicative_330_);
v___f_334_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_335_ = ((lean_object*)(l_Std_Iter_foldM___redArg___closed__0));
v___f_336_ = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__1), 2, 1);
lean_closure_set(v___f_336_, 0, v_toPure_333_);
v___f_337_ = lean_alloc_closure((void*)(l_Std_Iter_foldM___redArg___lam__2), 8, 5);
lean_closure_set(v___f_337_, 0, v_toFunctor_332_);
lean_closure_set(v___f_337_, 1, v_f_327_);
lean_closure_set(v___f_337_, 2, v___f_335_);
lean_closure_set(v___f_337_, 3, v_toBind_331_);
lean_closure_set(v___f_337_, 4, v___f_336_);
v___x_338_ = lean_apply_6(v_inst_325_, v___f_334_, lean_box(0), lean_box(0), v_it_329_, v_init_328_, v___f_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_foldM___boxed(lean_object* v_m_339_, lean_object* v_inst_340_, lean_object* v_00_u03b1_341_, lean_object* v_00_u03b2_342_, lean_object* v_00_u03b3_343_, lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_f_347_, lean_object* v_init_348_, lean_object* v_it_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Iter_Total_foldM(v_m_339_, v_inst_340_, v_00_u03b1_341_, v_00_u03b2_342_, v_00_u03b3_343_, v_inst_344_, v_inst_345_, v_inst_346_, v_f_347_, v_init_348_, v_it_349_);
lean_dec(v_inst_344_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_fold___redArg___lam__1(lean_object* v_f_351_, lean_object* v_x1_352_, lean_object* v_x2_353_, lean_object* v_x3_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_apply_2(v_f_351_, v_x3_354_, v_x1_352_);
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_fold___redArg(lean_object* v_inst_357_, lean_object* v_f_358_, lean_object* v_init_359_, lean_object* v_it_360_){
_start:
{
lean_object* v___f_361_; lean_object* v___f_362_; lean_object* v___x_363_; 
v___f_361_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_362_ = lean_alloc_closure((void*)(l_Std_Iter_fold___redArg___lam__1), 4, 1);
lean_closure_set(v___f_362_, 0, v_f_358_);
v___x_363_ = lean_apply_6(v_inst_357_, v___f_361_, lean_box(0), lean_box(0), v_it_360_, v_init_359_, v___f_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_fold(lean_object* v_00_u03b1_364_, lean_object* v_00_u03b2_365_, lean_object* v_00_u03b3_366_, lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_f_369_, lean_object* v_init_370_, lean_object* v_it_371_){
_start:
{
lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___x_374_; 
v___f_372_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_373_ = lean_alloc_closure((void*)(l_Std_Iter_fold___redArg___lam__1), 4, 1);
lean_closure_set(v___f_373_, 0, v_f_369_);
v___x_374_ = lean_apply_6(v_inst_368_, v___f_372_, lean_box(0), lean_box(0), v_it_371_, v_init_370_, v___f_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_fold___boxed(lean_object* v_00_u03b1_375_, lean_object* v_00_u03b2_376_, lean_object* v_00_u03b3_377_, lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_f_380_, lean_object* v_init_381_, lean_object* v_it_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_Iter_fold(v_00_u03b1_375_, v_00_u03b2_376_, v_00_u03b3_377_, v_inst_378_, v_inst_379_, v_f_380_, v_init_381_, v_it_382_);
lean_dec(v_inst_378_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_fold___redArg(lean_object* v_inst_384_, lean_object* v_f_385_, lean_object* v_init_386_, lean_object* v_it_387_){
_start:
{
lean_object* v___f_388_; lean_object* v___f_389_; lean_object* v___x_390_; 
v___f_388_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_389_ = lean_alloc_closure((void*)(l_Std_Iter_fold___redArg___lam__1), 4, 1);
lean_closure_set(v___f_389_, 0, v_f_385_);
v___x_390_ = lean_apply_6(v_inst_384_, v___f_388_, lean_box(0), lean_box(0), v_it_387_, v_init_386_, v___f_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_fold(lean_object* v_00_u03b1_391_, lean_object* v_00_u03b2_392_, lean_object* v_00_u03b3_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_f_397_, lean_object* v_init_398_, lean_object* v_it_399_){
_start:
{
lean_object* v___f_400_; lean_object* v___f_401_; lean_object* v___x_402_; 
v___f_400_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_401_ = lean_alloc_closure((void*)(l_Std_Iter_fold___redArg___lam__1), 4, 1);
lean_closure_set(v___f_401_, 0, v_f_397_);
v___x_402_ = lean_apply_6(v_inst_395_, v___f_400_, lean_box(0), lean_box(0), v_it_399_, v_init_398_, v___f_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_fold___boxed(lean_object* v_00_u03b1_403_, lean_object* v_00_u03b2_404_, lean_object* v_00_u03b3_405_, lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_f_409_, lean_object* v_init_410_, lean_object* v_it_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Std_Iter_Total_fold(v_00_u03b1_403_, v_00_u03b2_404_, v_00_u03b3_405_, v_inst_406_, v_inst_407_, v_inst_408_, v_f_409_, v_init_410_, v_it_411_);
lean_dec(v_inst_406_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__1(lean_object* v_toPure_413_, lean_object* v_____do__lift_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = lean_apply_2(v_toPure_413_, lean_box(0), v_____do__lift_414_);
return v___x_415_;
}
}
lean_object* l_Std_Iter_anyM___redArg___lam__0(uint8_t v___x_416_, lean_object* v_toPure_417_, uint8_t v_____do__lift_418_){
_start:
{
if (v_____do__lift_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_box(v___x_416_);
v___x_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
v___x_421_ = lean_apply_2(v_toPure_417_, lean_box(0), v___x_420_);
return v___x_421_;
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = lean_box(v_____do__lift_418_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
v___x_424_ = lean_apply_2(v_toPure_417_, lean_box(0), v___x_423_);
return v___x_424_;
}
}
}
LEAN_EXPORT void l_Std_Iter_anyM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_416_ = stack[0].m_num;
lean_object* v_toPure_417_ = stack[1].m_obj;
uint8_t v_____do__lift_418_ = stack[2].m_num;
lean_object* v_res_425_;
v_res_425_ = l_Std_Iter_anyM___redArg___lam__0(v___x_416_, v_toPure_417_, v_____do__lift_418_);
stack->m_obj
 = v_res_425_;
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__0___boxed(lean_object* v___x_426_, lean_object* v_toPure_427_, lean_object* v_____do__lift_428_){
_start:
{
uint8_t v___x_190__boxed_429_; uint8_t v_____do__lift_191__boxed_430_; lean_object* v_res_431_; 
v___x_190__boxed_429_ = lean_unbox(v___x_426_);
v_____do__lift_191__boxed_430_ = lean_unbox(v_____do__lift_428_);
v_res_431_ = l_Std_Iter_anyM___redArg___lam__0(v___x_190__boxed_429_, v_toPure_427_, v_____do__lift_191__boxed_430_);
return v_res_431_;
}
}
lean_object* l_Std_Iter_anyM___redArg___lam__2(lean_object* v_p_432_, lean_object* v_toBind_433_, lean_object* v___f_434_, lean_object* v___f_435_, lean_object* v_x1_436_, lean_object* v_x2_437_, uint8_t v_x3_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_apply_1(v_p_432_, v_x1_436_);
lean_inc(v_toBind_433_);
v___x_440_ = lean_apply_4(v_toBind_433_, lean_box(0), lean_box(0), v___x_439_, v___f_434_);
v___x_441_ = lean_apply_4(v_toBind_433_, lean_box(0), lean_box(0), v___x_440_, v___f_435_);
return v___x_441_;
}
}
LEAN_EXPORT void l_Std_Iter_anyM___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_432_ = stack[0].m_obj;
lean_object* v_toBind_433_ = stack[1].m_obj;
lean_object* v___f_434_ = stack[2].m_obj;
lean_object* v___f_435_ = stack[3].m_obj;
lean_object* v_x1_436_ = stack[4].m_obj;
uint8_t v_x3_438_ = stack[6].m_num;
lean_object* v_res_442_;
v_res_442_ = l_Std_Iter_anyM___redArg___lam__2(v_p_432_, v_toBind_433_, v___f_434_, v___f_435_, v_x1_436_, lean_box(0), v_x3_438_);
stack->m_obj
 = v_res_442_;
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__2___boxed(lean_object* v_p_443_, lean_object* v_toBind_444_, lean_object* v___f_445_, lean_object* v___f_446_, lean_object* v_x1_447_, lean_object* v_x2_448_, lean_object* v_x3_449_){
_start:
{
uint8_t v_x3_222__boxed_450_; lean_object* v_res_451_; 
v_x3_222__boxed_450_ = lean_unbox(v_x3_449_);
v_res_451_ = l_Std_Iter_anyM___redArg___lam__2(v_p_443_, v_toBind_444_, v___f_445_, v___f_446_, v_x1_447_, v_x2_448_, v_x3_222__boxed_450_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg(lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_p_454_, lean_object* v_it_455_){
_start:
{
lean_object* v_toApplicative_456_; lean_object* v_toBind_457_; lean_object* v_toPure_458_; lean_object* v___f_459_; uint8_t v___x_460_; lean_object* v___f_461_; lean_object* v___x_462_; lean_object* v___f_463_; lean_object* v___f_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_toApplicative_456_ = lean_ctor_get(v_inst_452_, 0);
lean_inc_ref(v_toApplicative_456_);
v_toBind_457_ = lean_ctor_get(v_inst_452_, 1);
lean_inc(v_toBind_457_);
lean_dec_ref(v_inst_452_);
v_toPure_458_ = lean_ctor_get(v_toApplicative_456_, 1);
lean_inc_n(v_toPure_458_, 2);
lean_dec_ref(v_toApplicative_456_);
v___f_459_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_460_ = 0;
v___f_461_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_461_, 0, v_toPure_458_);
v___x_462_ = lean_box(v___x_460_);
v___f_463_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_463_, 0, v___x_462_);
lean_closure_set(v___f_463_, 1, v_toPure_458_);
v___f_464_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_464_, 0, v_p_454_);
lean_closure_set(v___f_464_, 1, v_toBind_457_);
lean_closure_set(v___f_464_, 2, v___f_463_);
lean_closure_set(v___f_464_, 3, v___f_461_);
v___x_465_ = lean_box(v___x_460_);
v___x_466_ = lean_apply_6(v_inst_453_, v___f_459_, lean_box(0), lean_box(0), v_it_455_, v___x_465_, v___f_464_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM(lean_object* v_00_u03b1_467_, lean_object* v_00_u03b2_468_, lean_object* v_m_469_, lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_p_473_, lean_object* v_it_474_){
_start:
{
lean_object* v_toApplicative_475_; lean_object* v_toBind_476_; lean_object* v_toPure_477_; lean_object* v___f_478_; uint8_t v___x_479_; lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___f_482_; lean_object* v___f_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_toApplicative_475_ = lean_ctor_get(v_inst_470_, 0);
lean_inc_ref(v_toApplicative_475_);
v_toBind_476_ = lean_ctor_get(v_inst_470_, 1);
lean_inc(v_toBind_476_);
lean_dec_ref(v_inst_470_);
v_toPure_477_ = lean_ctor_get(v_toApplicative_475_, 1);
lean_inc_n(v_toPure_477_, 2);
lean_dec_ref(v_toApplicative_475_);
v___f_478_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_479_ = 0;
v___f_480_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_480_, 0, v_toPure_477_);
v___x_481_ = lean_box(v___x_479_);
v___f_482_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_482_, 0, v___x_481_);
lean_closure_set(v___f_482_, 1, v_toPure_477_);
v___f_483_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_483_, 0, v_p_473_);
lean_closure_set(v___f_483_, 1, v_toBind_476_);
lean_closure_set(v___f_483_, 2, v___f_482_);
lean_closure_set(v___f_483_, 3, v___f_480_);
v___x_484_ = lean_box(v___x_479_);
v___x_485_ = lean_apply_6(v_inst_472_, v___f_478_, lean_box(0), lean_box(0), v_it_474_, v___x_484_, v___f_483_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___boxed(lean_object* v_00_u03b1_486_, lean_object* v_00_u03b2_487_, lean_object* v_m_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_p_492_, lean_object* v_it_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Std_Iter_anyM(v_00_u03b1_486_, v_00_u03b2_487_, v_m_488_, v_inst_489_, v_inst_490_, v_inst_491_, v_p_492_, v_it_493_);
lean_dec(v_inst_490_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_anyM___redArg(lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_p_497_, lean_object* v_it_498_){
_start:
{
lean_object* v_toApplicative_499_; lean_object* v_toBind_500_; lean_object* v_toPure_501_; lean_object* v___f_502_; uint8_t v___x_503_; lean_object* v___x_504_; lean_object* v___f_505_; lean_object* v___f_506_; lean_object* v___f_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v_toApplicative_499_ = lean_ctor_get(v_inst_495_, 0);
lean_inc_ref(v_toApplicative_499_);
v_toBind_500_ = lean_ctor_get(v_inst_495_, 1);
lean_inc(v_toBind_500_);
lean_dec_ref(v_inst_495_);
v_toPure_501_ = lean_ctor_get(v_toApplicative_499_, 1);
lean_inc_n(v_toPure_501_, 2);
lean_dec_ref(v_toApplicative_499_);
v___f_502_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_503_ = 0;
v___x_504_ = lean_box(v___x_503_);
v___f_505_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_505_, 0, v___x_504_);
lean_closure_set(v___f_505_, 1, v_toPure_501_);
v___f_506_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_506_, 0, v_toPure_501_);
v___f_507_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_507_, 0, v_p_497_);
lean_closure_set(v___f_507_, 1, v_toBind_500_);
lean_closure_set(v___f_507_, 2, v___f_505_);
lean_closure_set(v___f_507_, 3, v___f_506_);
v___x_508_ = lean_box(v___x_503_);
v___x_509_ = lean_apply_6(v_inst_496_, v___f_502_, lean_box(0), lean_box(0), v_it_498_, v___x_508_, v___f_507_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_anyM(lean_object* v_00_u03b1_510_, lean_object* v_00_u03b2_511_, lean_object* v_m_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_p_517_, lean_object* v_it_518_){
_start:
{
lean_object* v_toApplicative_519_; lean_object* v_toBind_520_; lean_object* v_toPure_521_; lean_object* v___f_522_; uint8_t v___x_523_; lean_object* v___x_524_; lean_object* v___f_525_; lean_object* v___f_526_; lean_object* v___f_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v_toApplicative_519_ = lean_ctor_get(v_inst_513_, 0);
lean_inc_ref(v_toApplicative_519_);
v_toBind_520_ = lean_ctor_get(v_inst_513_, 1);
lean_inc(v_toBind_520_);
lean_dec_ref(v_inst_513_);
v_toPure_521_ = lean_ctor_get(v_toApplicative_519_, 1);
lean_inc_n(v_toPure_521_, 2);
lean_dec_ref(v_toApplicative_519_);
v___f_522_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_523_ = 0;
v___x_524_ = lean_box(v___x_523_);
v___f_525_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_525_, 0, v___x_524_);
lean_closure_set(v___f_525_, 1, v_toPure_521_);
v___f_526_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_526_, 0, v_toPure_521_);
v___f_527_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_527_, 0, v_p_517_);
lean_closure_set(v___f_527_, 1, v_toBind_520_);
lean_closure_set(v___f_527_, 2, v___f_525_);
lean_closure_set(v___f_527_, 3, v___f_526_);
v___x_528_ = lean_box(v___x_523_);
v___x_529_ = lean_apply_6(v_inst_515_, v___f_522_, lean_box(0), lean_box(0), v_it_518_, v___x_528_, v___f_527_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_anyM___boxed(lean_object* v_00_u03b1_530_, lean_object* v_00_u03b2_531_, lean_object* v_m_532_, lean_object* v_inst_533_, lean_object* v_inst_534_, lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_p_537_, lean_object* v_it_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Std_Iter_Total_anyM(v_00_u03b1_530_, v_00_u03b2_531_, v_m_532_, v_inst_533_, v_inst_534_, v_inst_535_, v_inst_536_, v_p_537_, v_it_538_);
lean_dec(v_inst_534_);
return v_res_539_;
}
}
lean_object* l_Std_Iter_any___redArg___lam__1(lean_object* v_p_540_, uint8_t v___x_541_, lean_object* v_x1_542_, lean_object* v_x2_543_, uint8_t v_x3_544_){
_start:
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_apply_1(v_p_540_, v_x1_542_);
v___x_546_ = lean_unbox(v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_box(v___x_541_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
else
{
lean_object* v___x_549_; 
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_545_);
return v___x_549_;
}
}
}
LEAN_EXPORT void l_Std_Iter_any___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_540_ = stack[0].m_obj;
uint8_t v___x_541_ = stack[1].m_num;
lean_object* v_x1_542_ = stack[2].m_obj;
uint8_t v_x3_544_ = stack[4].m_num;
lean_object* v_res_550_;
v_res_550_ = l_Std_Iter_any___redArg___lam__1(v_p_540_, v___x_541_, v_x1_542_, lean_box(0), v_x3_544_);
stack->m_obj
 = v_res_550_;
}
LEAN_EXPORT lean_object* l_Std_Iter_any___redArg___lam__1___boxed(lean_object* v_p_551_, lean_object* v___x_552_, lean_object* v_x1_553_, lean_object* v_x2_554_, lean_object* v_x3_555_){
_start:
{
uint8_t v___x_276__boxed_556_; uint8_t v_x3_279__boxed_557_; lean_object* v_res_558_; 
v___x_276__boxed_556_ = lean_unbox(v___x_552_);
v_x3_279__boxed_557_ = lean_unbox(v_x3_555_);
v_res_558_ = l_Std_Iter_any___redArg___lam__1(v_p_551_, v___x_276__boxed_556_, v_x1_553_, v_x2_554_, v_x3_279__boxed_557_);
return v_res_558_;
}
}
uint8_t l_Std_Iter_any___redArg(lean_object* v_inst_559_, lean_object* v_p_560_, lean_object* v_it_561_){
_start:
{
lean_object* v___f_562_; uint8_t v___x_563_; lean_object* v___x_564_; lean_object* v___f_565_; lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___f_562_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_563_ = 0;
v___x_564_ = lean_box(v___x_563_);
v___f_565_ = lean_alloc_closure((void*)(l_Std_Iter_any___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_565_, 0, v_p_560_);
lean_closure_set(v___f_565_, 1, v___x_564_);
v___x_566_ = lean_box(v___x_563_);
v___x_567_ = lean_apply_6(v_inst_559_, v___f_562_, lean_box(0), lean_box(0), v_it_561_, v___x_566_, v___f_565_);
v___x_568_ = lean_unbox(v___x_567_);
return v___x_568_;
}
}
LEAN_EXPORT void l_Std_Iter_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_559_ = stack[0].m_obj;
lean_object* v_p_560_ = stack[1].m_obj;
lean_object* v_it_561_ = stack[2].m_obj;
uint8_t v_res_569_;
v_res_569_ = l_Std_Iter_any___redArg(v_inst_559_, v_p_560_, v_it_561_);
stack->m_num = v_res_569_;
}
LEAN_EXPORT lean_object* l_Std_Iter_any___redArg___boxed(lean_object* v_inst_570_, lean_object* v_p_571_, lean_object* v_it_572_){
_start:
{
uint8_t v_res_573_; lean_object* v_r_574_; 
v_res_573_ = l_Std_Iter_any___redArg(v_inst_570_, v_p_571_, v_it_572_);
v_r_574_ = lean_box(v_res_573_);
return v_r_574_;
}
}
uint8_t l_Std_Iter_any(lean_object* v_00_u03b1_575_, lean_object* v_00_u03b2_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_p_579_, lean_object* v_it_580_){
_start:
{
lean_object* v___f_581_; uint8_t v___x_582_; lean_object* v___x_583_; lean_object* v___f_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___f_581_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_582_ = 0;
v___x_583_ = lean_box(v___x_582_);
v___f_584_ = lean_alloc_closure((void*)(l_Std_Iter_any___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_584_, 0, v_p_579_);
lean_closure_set(v___f_584_, 1, v___x_583_);
v___x_585_ = lean_box(v___x_582_);
v___x_586_ = lean_apply_6(v_inst_578_, v___f_581_, lean_box(0), lean_box(0), v_it_580_, v___x_585_, v___f_584_);
v___x_587_ = lean_unbox(v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT void l_Std_Iter_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_577_ = stack[2].m_obj;
lean_object* v_inst_578_ = stack[3].m_obj;
lean_object* v_p_579_ = stack[4].m_obj;
lean_object* v_it_580_ = stack[5].m_obj;
uint8_t v_res_588_;
v_res_588_ = l_Std_Iter_any(lean_box(0), lean_box(0), v_inst_577_, v_inst_578_, v_p_579_, v_it_580_);
stack->m_num = v_res_588_;
}
LEAN_EXPORT lean_object* l_Std_Iter_any___boxed(lean_object* v_00_u03b1_589_, lean_object* v_00_u03b2_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_p_593_, lean_object* v_it_594_){
_start:
{
uint8_t v_res_595_; lean_object* v_r_596_; 
v_res_595_ = l_Std_Iter_any(v_00_u03b1_589_, v_00_u03b2_590_, v_inst_591_, v_inst_592_, v_p_593_, v_it_594_);
lean_dec(v_inst_591_);
v_r_596_ = lean_box(v_res_595_);
return v_r_596_;
}
}
uint8_t l_Std_Iter_Total_any___redArg(lean_object* v_inst_597_, lean_object* v_p_598_, lean_object* v_it_599_){
_start:
{
lean_object* v___f_600_; uint8_t v___x_601_; lean_object* v___x_602_; lean_object* v___f_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___f_600_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_601_ = 0;
v___x_602_ = lean_box(v___x_601_);
v___f_603_ = lean_alloc_closure((void*)(l_Std_Iter_any___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_603_, 0, v_p_598_);
lean_closure_set(v___f_603_, 1, v___x_602_);
v___x_604_ = lean_box(v___x_601_);
v___x_605_ = lean_apply_6(v_inst_597_, v___f_600_, lean_box(0), lean_box(0), v_it_599_, v___x_604_, v___f_603_);
v___x_606_ = lean_unbox(v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT void l_Std_Iter_Total_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_597_ = stack[0].m_obj;
lean_object* v_p_598_ = stack[1].m_obj;
lean_object* v_it_599_ = stack[2].m_obj;
uint8_t v_res_607_;
v_res_607_ = l_Std_Iter_Total_any___redArg(v_inst_597_, v_p_598_, v_it_599_);
stack->m_num = v_res_607_;
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_any___redArg___boxed(lean_object* v_inst_608_, lean_object* v_p_609_, lean_object* v_it_610_){
_start:
{
uint8_t v_res_611_; lean_object* v_r_612_; 
v_res_611_ = l_Std_Iter_Total_any___redArg(v_inst_608_, v_p_609_, v_it_610_);
v_r_612_ = lean_box(v_res_611_);
return v_r_612_;
}
}
uint8_t l_Std_Iter_Total_any(lean_object* v_00_u03b1_613_, lean_object* v_00_u03b2_614_, lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_inst_617_, lean_object* v_p_618_, lean_object* v_it_619_){
_start:
{
lean_object* v___f_620_; uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___f_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___f_620_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_621_ = 0;
v___x_622_ = lean_box(v___x_621_);
v___f_623_ = lean_alloc_closure((void*)(l_Std_Iter_any___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_623_, 0, v_p_618_);
lean_closure_set(v___f_623_, 1, v___x_622_);
v___x_624_ = lean_box(v___x_621_);
v___x_625_ = lean_apply_6(v_inst_616_, v___f_620_, lean_box(0), lean_box(0), v_it_619_, v___x_624_, v___f_623_);
v___x_626_ = lean_unbox(v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT void l_Std_Iter_Total_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_615_ = stack[2].m_obj;
lean_object* v_inst_616_ = stack[3].m_obj;
lean_object* v_p_618_ = stack[5].m_obj;
lean_object* v_it_619_ = stack[6].m_obj;
uint8_t v_res_627_;
v_res_627_ = l_Std_Iter_Total_any(lean_box(0), lean_box(0), v_inst_615_, v_inst_616_, lean_box(0), v_p_618_, v_it_619_);
stack->m_num = v_res_627_;
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_any___boxed(lean_object* v_00_u03b1_628_, lean_object* v_00_u03b2_629_, lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_p_633_, lean_object* v_it_634_){
_start:
{
uint8_t v_res_635_; lean_object* v_r_636_; 
v_res_635_ = l_Std_Iter_Total_any(v_00_u03b1_628_, v_00_u03b2_629_, v_inst_630_, v_inst_631_, v_inst_632_, v_p_633_, v_it_634_);
lean_dec(v_inst_630_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
lean_object* l_Std_Iter_allM___redArg___lam__2(lean_object* v_toPure_637_, uint8_t v___x_638_, uint8_t v_____do__lift_639_){
_start:
{
if (v_____do__lift_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = lean_box(v_____do__lift_639_);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
v___x_642_ = lean_apply_2(v_toPure_637_, lean_box(0), v___x_641_);
return v___x_642_;
}
else
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = lean_box(v___x_638_);
v___x_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
v___x_645_ = lean_apply_2(v_toPure_637_, lean_box(0), v___x_644_);
return v___x_645_;
}
}
}
LEAN_EXPORT void l_Std_Iter_allM___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_637_ = stack[0].m_obj;
uint8_t v___x_638_ = stack[1].m_num;
uint8_t v_____do__lift_639_ = stack[2].m_num;
lean_object* v_res_646_;
v_res_646_ = l_Std_Iter_allM___redArg___lam__2(v_toPure_637_, v___x_638_, v_____do__lift_639_);
stack->m_obj
 = v_res_646_;
}
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg___lam__2___boxed(lean_object* v_toPure_647_, lean_object* v___x_648_, lean_object* v_____do__lift_649_){
_start:
{
uint8_t v___x_182__boxed_650_; uint8_t v_____do__lift_183__boxed_651_; lean_object* v_res_652_; 
v___x_182__boxed_650_ = lean_unbox(v___x_648_);
v_____do__lift_183__boxed_651_ = lean_unbox(v_____do__lift_649_);
v_res_652_ = l_Std_Iter_allM___redArg___lam__2(v_toPure_647_, v___x_182__boxed_650_, v_____do__lift_183__boxed_651_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg(lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_p_655_, lean_object* v_it_656_){
_start:
{
lean_object* v_toApplicative_657_; lean_object* v_toBind_658_; lean_object* v_toPure_659_; lean_object* v___f_660_; uint8_t v___x_661_; lean_object* v___f_662_; lean_object* v___x_663_; lean_object* v___f_664_; lean_object* v___f_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_toApplicative_657_ = lean_ctor_get(v_inst_653_, 0);
lean_inc_ref(v_toApplicative_657_);
v_toBind_658_ = lean_ctor_get(v_inst_653_, 1);
lean_inc(v_toBind_658_);
lean_dec_ref(v_inst_653_);
v_toPure_659_ = lean_ctor_get(v_toApplicative_657_, 1);
lean_inc_n(v_toPure_659_, 2);
lean_dec_ref(v_toApplicative_657_);
v___f_660_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_661_ = 1;
v___f_662_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_662_, 0, v_toPure_659_);
v___x_663_ = lean_box(v___x_661_);
v___f_664_ = lean_alloc_closure((void*)(l_Std_Iter_allM___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_664_, 0, v_toPure_659_);
lean_closure_set(v___f_664_, 1, v___x_663_);
v___f_665_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_665_, 0, v_p_655_);
lean_closure_set(v___f_665_, 1, v_toBind_658_);
lean_closure_set(v___f_665_, 2, v___f_664_);
lean_closure_set(v___f_665_, 3, v___f_662_);
v___x_666_ = lean_box(v___x_661_);
v___x_667_ = lean_apply_6(v_inst_654_, v___f_660_, lean_box(0), lean_box(0), v_it_656_, v___x_666_, v___f_665_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_allM(lean_object* v_00_u03b1_668_, lean_object* v_00_u03b2_669_, lean_object* v_m_670_, lean_object* v_inst_671_, lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_p_674_, lean_object* v_it_675_){
_start:
{
lean_object* v_toApplicative_676_; lean_object* v_toBind_677_; lean_object* v_toPure_678_; lean_object* v___f_679_; uint8_t v___x_680_; lean_object* v___f_681_; lean_object* v___x_682_; lean_object* v___f_683_; lean_object* v___f_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v_toApplicative_676_ = lean_ctor_get(v_inst_671_, 0);
lean_inc_ref(v_toApplicative_676_);
v_toBind_677_ = lean_ctor_get(v_inst_671_, 1);
lean_inc(v_toBind_677_);
lean_dec_ref(v_inst_671_);
v_toPure_678_ = lean_ctor_get(v_toApplicative_676_, 1);
lean_inc_n(v_toPure_678_, 2);
lean_dec_ref(v_toApplicative_676_);
v___f_679_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_680_ = 1;
v___f_681_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_681_, 0, v_toPure_678_);
v___x_682_ = lean_box(v___x_680_);
v___f_683_ = lean_alloc_closure((void*)(l_Std_Iter_allM___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_683_, 0, v_toPure_678_);
lean_closure_set(v___f_683_, 1, v___x_682_);
v___f_684_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_684_, 0, v_p_674_);
lean_closure_set(v___f_684_, 1, v_toBind_677_);
lean_closure_set(v___f_684_, 2, v___f_683_);
lean_closure_set(v___f_684_, 3, v___f_681_);
v___x_685_ = lean_box(v___x_680_);
v___x_686_ = lean_apply_6(v_inst_673_, v___f_679_, lean_box(0), lean_box(0), v_it_675_, v___x_685_, v___f_684_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_allM___boxed(lean_object* v_00_u03b1_687_, lean_object* v_00_u03b2_688_, lean_object* v_m_689_, lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_p_693_, lean_object* v_it_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Std_Iter_allM(v_00_u03b1_687_, v_00_u03b2_688_, v_m_689_, v_inst_690_, v_inst_691_, v_inst_692_, v_p_693_, v_it_694_);
lean_dec(v_inst_691_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_allM___redArg(lean_object* v_inst_696_, lean_object* v_inst_697_, lean_object* v_p_698_, lean_object* v_it_699_){
_start:
{
lean_object* v_toApplicative_700_; lean_object* v_toBind_701_; lean_object* v_toPure_702_; lean_object* v___f_703_; uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v___f_706_; lean_object* v___f_707_; lean_object* v___f_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v_toApplicative_700_ = lean_ctor_get(v_inst_696_, 0);
lean_inc_ref(v_toApplicative_700_);
v_toBind_701_ = lean_ctor_get(v_inst_696_, 1);
lean_inc(v_toBind_701_);
lean_dec_ref(v_inst_696_);
v_toPure_702_ = lean_ctor_get(v_toApplicative_700_, 1);
lean_inc_n(v_toPure_702_, 2);
lean_dec_ref(v_toApplicative_700_);
v___f_703_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_704_ = 1;
v___x_705_ = lean_box(v___x_704_);
v___f_706_ = lean_alloc_closure((void*)(l_Std_Iter_allM___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_706_, 0, v_toPure_702_);
lean_closure_set(v___f_706_, 1, v___x_705_);
v___f_707_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_707_, 0, v_toPure_702_);
v___f_708_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_708_, 0, v_p_698_);
lean_closure_set(v___f_708_, 1, v_toBind_701_);
lean_closure_set(v___f_708_, 2, v___f_706_);
lean_closure_set(v___f_708_, 3, v___f_707_);
v___x_709_ = lean_box(v___x_704_);
v___x_710_ = lean_apply_6(v_inst_697_, v___f_703_, lean_box(0), lean_box(0), v_it_699_, v___x_709_, v___f_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_allM(lean_object* v_00_u03b1_711_, lean_object* v_00_u03b2_712_, lean_object* v_m_713_, lean_object* v_inst_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_inst_717_, lean_object* v_p_718_, lean_object* v_it_719_){
_start:
{
lean_object* v_toApplicative_720_; lean_object* v_toBind_721_; lean_object* v_toPure_722_; lean_object* v___f_723_; uint8_t v___x_724_; lean_object* v___x_725_; lean_object* v___f_726_; lean_object* v___f_727_; lean_object* v___f_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_toApplicative_720_ = lean_ctor_get(v_inst_714_, 0);
lean_inc_ref(v_toApplicative_720_);
v_toBind_721_ = lean_ctor_get(v_inst_714_, 1);
lean_inc(v_toBind_721_);
lean_dec_ref(v_inst_714_);
v_toPure_722_ = lean_ctor_get(v_toApplicative_720_, 1);
lean_inc_n(v_toPure_722_, 2);
lean_dec_ref(v_toApplicative_720_);
v___f_723_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_724_ = 1;
v___x_725_ = lean_box(v___x_724_);
v___f_726_ = lean_alloc_closure((void*)(l_Std_Iter_allM___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_726_, 0, v_toPure_722_);
lean_closure_set(v___f_726_, 1, v___x_725_);
v___f_727_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_727_, 0, v_toPure_722_);
v___f_728_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_728_, 0, v_p_718_);
lean_closure_set(v___f_728_, 1, v_toBind_721_);
lean_closure_set(v___f_728_, 2, v___f_726_);
lean_closure_set(v___f_728_, 3, v___f_727_);
v___x_729_ = lean_box(v___x_724_);
v___x_730_ = lean_apply_6(v_inst_716_, v___f_723_, lean_box(0), lean_box(0), v_it_719_, v___x_729_, v___f_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_allM___boxed(lean_object* v_00_u03b1_731_, lean_object* v_00_u03b2_732_, lean_object* v_m_733_, lean_object* v_inst_734_, lean_object* v_inst_735_, lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_p_738_, lean_object* v_it_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Std_Iter_Total_allM(v_00_u03b1_731_, v_00_u03b2_732_, v_m_733_, v_inst_734_, v_inst_735_, v_inst_736_, v_inst_737_, v_p_738_, v_it_739_);
lean_dec(v_inst_735_);
return v_res_740_;
}
}
lean_object* l_Std_Iter_all___redArg___lam__1(lean_object* v_p_741_, uint8_t v___x_742_, lean_object* v_x1_743_, lean_object* v_x2_744_, uint8_t v_x3_745_){
_start:
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = lean_apply_1(v_p_741_, v_x1_743_);
v___x_747_ = lean_unbox(v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; 
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_746_);
return v___x_748_;
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_box(v___x_742_);
v___x_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
}
}
LEAN_EXPORT void l_Std_Iter_all___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_741_ = stack[0].m_obj;
uint8_t v___x_742_ = stack[1].m_num;
lean_object* v_x1_743_ = stack[2].m_obj;
uint8_t v_x3_745_ = stack[4].m_num;
lean_object* v_res_751_;
v_res_751_ = l_Std_Iter_all___redArg___lam__1(v_p_741_, v___x_742_, v_x1_743_, lean_box(0), v_x3_745_);
stack->m_obj
 = v_res_751_;
}
LEAN_EXPORT lean_object* l_Std_Iter_all___redArg___lam__1___boxed(lean_object* v_p_752_, lean_object* v___x_753_, lean_object* v_x1_754_, lean_object* v_x2_755_, lean_object* v_x3_756_){
_start:
{
uint8_t v___x_276__boxed_757_; uint8_t v_x3_279__boxed_758_; lean_object* v_res_759_; 
v___x_276__boxed_757_ = lean_unbox(v___x_753_);
v_x3_279__boxed_758_ = lean_unbox(v_x3_756_);
v_res_759_ = l_Std_Iter_all___redArg___lam__1(v_p_752_, v___x_276__boxed_757_, v_x1_754_, v_x2_755_, v_x3_279__boxed_758_);
return v_res_759_;
}
}
uint8_t l_Std_Iter_all___redArg(lean_object* v_inst_760_, lean_object* v_p_761_, lean_object* v_it_762_){
_start:
{
lean_object* v___f_763_; uint8_t v___x_764_; lean_object* v___x_765_; lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v___f_763_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_764_ = 1;
v___x_765_ = lean_box(v___x_764_);
v___f_766_ = lean_alloc_closure((void*)(l_Std_Iter_all___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_766_, 0, v_p_761_);
lean_closure_set(v___f_766_, 1, v___x_765_);
v___x_767_ = lean_box(v___x_764_);
v___x_768_ = lean_apply_6(v_inst_760_, v___f_763_, lean_box(0), lean_box(0), v_it_762_, v___x_767_, v___f_766_);
v___x_769_ = lean_unbox(v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT void l_Std_Iter_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_760_ = stack[0].m_obj;
lean_object* v_p_761_ = stack[1].m_obj;
lean_object* v_it_762_ = stack[2].m_obj;
uint8_t v_res_770_;
v_res_770_ = l_Std_Iter_all___redArg(v_inst_760_, v_p_761_, v_it_762_);
stack->m_num = v_res_770_;
}
LEAN_EXPORT lean_object* l_Std_Iter_all___redArg___boxed(lean_object* v_inst_771_, lean_object* v_p_772_, lean_object* v_it_773_){
_start:
{
uint8_t v_res_774_; lean_object* v_r_775_; 
v_res_774_ = l_Std_Iter_all___redArg(v_inst_771_, v_p_772_, v_it_773_);
v_r_775_ = lean_box(v_res_774_);
return v_r_775_;
}
}
uint8_t l_Std_Iter_all(lean_object* v_00_u03b1_776_, lean_object* v_00_u03b2_777_, lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_p_780_, lean_object* v_it_781_){
_start:
{
lean_object* v___f_782_; uint8_t v___x_783_; lean_object* v___x_784_; lean_object* v___f_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v___f_782_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_783_ = 1;
v___x_784_ = lean_box(v___x_783_);
v___f_785_ = lean_alloc_closure((void*)(l_Std_Iter_all___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_785_, 0, v_p_780_);
lean_closure_set(v___f_785_, 1, v___x_784_);
v___x_786_ = lean_box(v___x_783_);
v___x_787_ = lean_apply_6(v_inst_779_, v___f_782_, lean_box(0), lean_box(0), v_it_781_, v___x_786_, v___f_785_);
v___x_788_ = lean_unbox(v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT void l_Std_Iter_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_778_ = stack[2].m_obj;
lean_object* v_inst_779_ = stack[3].m_obj;
lean_object* v_p_780_ = stack[4].m_obj;
lean_object* v_it_781_ = stack[5].m_obj;
uint8_t v_res_789_;
v_res_789_ = l_Std_Iter_all(lean_box(0), lean_box(0), v_inst_778_, v_inst_779_, v_p_780_, v_it_781_);
stack->m_num = v_res_789_;
}
LEAN_EXPORT lean_object* l_Std_Iter_all___boxed(lean_object* v_00_u03b1_790_, lean_object* v_00_u03b2_791_, lean_object* v_inst_792_, lean_object* v_inst_793_, lean_object* v_p_794_, lean_object* v_it_795_){
_start:
{
uint8_t v_res_796_; lean_object* v_r_797_; 
v_res_796_ = l_Std_Iter_all(v_00_u03b1_790_, v_00_u03b2_791_, v_inst_792_, v_inst_793_, v_p_794_, v_it_795_);
lean_dec(v_inst_792_);
v_r_797_ = lean_box(v_res_796_);
return v_r_797_;
}
}
uint8_t l_Std_Iter_Total_all___redArg(lean_object* v_inst_798_, lean_object* v_p_799_, lean_object* v_it_800_){
_start:
{
lean_object* v___f_801_; uint8_t v___x_802_; lean_object* v___x_803_; lean_object* v___f_804_; lean_object* v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v___f_801_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_802_ = 1;
v___x_803_ = lean_box(v___x_802_);
v___f_804_ = lean_alloc_closure((void*)(l_Std_Iter_all___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_804_, 0, v_p_799_);
lean_closure_set(v___f_804_, 1, v___x_803_);
v___x_805_ = lean_box(v___x_802_);
v___x_806_ = lean_apply_6(v_inst_798_, v___f_801_, lean_box(0), lean_box(0), v_it_800_, v___x_805_, v___f_804_);
v___x_807_ = lean_unbox(v___x_806_);
return v___x_807_;
}
}
LEAN_EXPORT void l_Std_Iter_Total_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_798_ = stack[0].m_obj;
lean_object* v_p_799_ = stack[1].m_obj;
lean_object* v_it_800_ = stack[2].m_obj;
uint8_t v_res_808_;
v_res_808_ = l_Std_Iter_Total_all___redArg(v_inst_798_, v_p_799_, v_it_800_);
stack->m_num = v_res_808_;
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_all___redArg___boxed(lean_object* v_inst_809_, lean_object* v_p_810_, lean_object* v_it_811_){
_start:
{
uint8_t v_res_812_; lean_object* v_r_813_; 
v_res_812_ = l_Std_Iter_Total_all___redArg(v_inst_809_, v_p_810_, v_it_811_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
uint8_t l_Std_Iter_Total_all(lean_object* v_00_u03b1_814_, lean_object* v_00_u03b2_815_, lean_object* v_inst_816_, lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_p_819_, lean_object* v_it_820_){
_start:
{
lean_object* v___f_821_; uint8_t v___x_822_; lean_object* v___x_823_; lean_object* v___f_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v___f_821_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_822_ = 1;
v___x_823_ = lean_box(v___x_822_);
v___f_824_ = lean_alloc_closure((void*)(l_Std_Iter_all___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_824_, 0, v_p_819_);
lean_closure_set(v___f_824_, 1, v___x_823_);
v___x_825_ = lean_box(v___x_822_);
v___x_826_ = lean_apply_6(v_inst_817_, v___f_821_, lean_box(0), lean_box(0), v_it_820_, v___x_825_, v___f_824_);
v___x_827_ = lean_unbox(v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT void l_Std_Iter_Total_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_816_ = stack[2].m_obj;
lean_object* v_inst_817_ = stack[3].m_obj;
lean_object* v_p_819_ = stack[5].m_obj;
lean_object* v_it_820_ = stack[6].m_obj;
uint8_t v_res_828_;
v_res_828_ = l_Std_Iter_Total_all(lean_box(0), lean_box(0), v_inst_816_, v_inst_817_, lean_box(0), v_p_819_, v_it_820_);
stack->m_num = v_res_828_;
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_all___boxed(lean_object* v_00_u03b1_829_, lean_object* v_00_u03b2_830_, lean_object* v_inst_831_, lean_object* v_inst_832_, lean_object* v_inst_833_, lean_object* v_p_834_, lean_object* v_it_835_){
_start:
{
uint8_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l_Std_Iter_Total_all(v_00_u03b1_829_, v_00_u03b2_830_, v_inst_831_, v_inst_832_, v_inst_833_, v_p_834_, v_it_835_);
lean_dec(v_inst_831_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__1(lean_object* v_toPure_838_, lean_object* v_____do__lift_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = lean_apply_2(v_toPure_838_, lean_box(0), v_____do__lift_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__0(lean_object* v___x_841_, lean_object* v_toPure_842_, lean_object* v_____do__lift_843_){
_start:
{
if (lean_obj_tag(v_____do__lift_843_) == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_841_);
v___x_845_ = lean_apply_2(v_toPure_842_, lean_box(0), v___x_844_);
return v___x_845_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec(v___x_841_);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v_____do__lift_843_);
v___x_847_ = lean_apply_2(v_toPure_842_, lean_box(0), v___x_846_);
return v___x_847_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__2(lean_object* v_f_848_, lean_object* v_toBind_849_, lean_object* v___f_850_, lean_object* v___f_851_, lean_object* v_x1_852_, lean_object* v_x2_853_, lean_object* v_x3_854_){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = lean_apply_1(v_f_848_, v_x1_852_);
lean_inc(v_toBind_849_);
v___x_856_ = lean_apply_4(v_toBind_849_, lean_box(0), lean_box(0), v___x_855_, v___f_850_);
v___x_857_ = lean_apply_4(v_toBind_849_, lean_box(0), lean_box(0), v___x_856_, v___f_851_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed(lean_object* v_f_858_, lean_object* v_toBind_859_, lean_object* v___f_860_, lean_object* v___f_861_, lean_object* v_x1_862_, lean_object* v_x2_863_, lean_object* v_x3_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Std_Iter_findSomeM_x3f___redArg___lam__2(v_f_858_, v_toBind_859_, v___f_860_, v___f_861_, v_x1_862_, v_x2_863_, v_x3_864_);
lean_dec(v_x3_864_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg(lean_object* v_inst_866_, lean_object* v_inst_867_, lean_object* v_it_868_, lean_object* v_f_869_){
_start:
{
lean_object* v_toApplicative_870_; lean_object* v_toBind_871_; lean_object* v_toPure_872_; lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v___f_875_; lean_object* v___f_876_; lean_object* v___f_877_; lean_object* v___x_878_; 
v_toApplicative_870_ = lean_ctor_get(v_inst_866_, 0);
lean_inc_ref(v_toApplicative_870_);
v_toBind_871_ = lean_ctor_get(v_inst_866_, 1);
lean_inc(v_toBind_871_);
lean_dec_ref(v_inst_866_);
v_toPure_872_ = lean_ctor_get(v_toApplicative_870_, 1);
lean_inc_n(v_toPure_872_, 2);
lean_dec_ref(v_toApplicative_870_);
v___f_873_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_874_ = lean_box(0);
v___f_875_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_875_, 0, v_toPure_872_);
v___f_876_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_876_, 0, v___x_874_);
lean_closure_set(v___f_876_, 1, v_toPure_872_);
v___f_877_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_877_, 0, v_f_869_);
lean_closure_set(v___f_877_, 1, v_toBind_871_);
lean_closure_set(v___f_877_, 2, v___f_876_);
lean_closure_set(v___f_877_, 3, v___f_875_);
v___x_878_ = lean_apply_6(v_inst_867_, v___f_873_, lean_box(0), lean_box(0), v_it_868_, v___x_874_, v___f_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f(lean_object* v_00_u03b1_879_, lean_object* v_00_u03b2_880_, lean_object* v_00_u03b3_881_, lean_object* v_m_882_, lean_object* v_inst_883_, lean_object* v_inst_884_, lean_object* v_inst_885_, lean_object* v_it_886_, lean_object* v_f_887_){
_start:
{
lean_object* v_toApplicative_888_; lean_object* v_toBind_889_; lean_object* v_toPure_890_; lean_object* v___f_891_; lean_object* v___x_892_; lean_object* v___f_893_; lean_object* v___f_894_; lean_object* v___f_895_; lean_object* v___x_896_; 
v_toApplicative_888_ = lean_ctor_get(v_inst_883_, 0);
lean_inc_ref(v_toApplicative_888_);
v_toBind_889_ = lean_ctor_get(v_inst_883_, 1);
lean_inc(v_toBind_889_);
lean_dec_ref(v_inst_883_);
v_toPure_890_ = lean_ctor_get(v_toApplicative_888_, 1);
lean_inc_n(v_toPure_890_, 2);
lean_dec_ref(v_toApplicative_888_);
v___f_891_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_892_ = lean_box(0);
v___f_893_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_893_, 0, v_toPure_890_);
v___f_894_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_894_, 0, v___x_892_);
lean_closure_set(v___f_894_, 1, v_toPure_890_);
v___f_895_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_895_, 0, v_f_887_);
lean_closure_set(v___f_895_, 1, v_toBind_889_);
lean_closure_set(v___f_895_, 2, v___f_894_);
lean_closure_set(v___f_895_, 3, v___f_893_);
v___x_896_ = lean_apply_6(v_inst_885_, v___f_891_, lean_box(0), lean_box(0), v_it_886_, v___x_892_, v___f_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___boxed(lean_object* v_00_u03b1_897_, lean_object* v_00_u03b2_898_, lean_object* v_00_u03b3_899_, lean_object* v_m_900_, lean_object* v_inst_901_, lean_object* v_inst_902_, lean_object* v_inst_903_, lean_object* v_it_904_, lean_object* v_f_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Std_Iter_findSomeM_x3f(v_00_u03b1_897_, v_00_u03b2_898_, v_00_u03b3_899_, v_m_900_, v_inst_901_, v_inst_902_, v_inst_903_, v_it_904_, v_f_905_);
lean_dec(v_inst_902_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f___redArg(lean_object* v_inst_907_, lean_object* v_inst_908_, lean_object* v_it_909_, lean_object* v_f_910_){
_start:
{
lean_object* v_toApplicative_911_; lean_object* v_toBind_912_; lean_object* v_toPure_913_; lean_object* v___f_914_; lean_object* v___x_915_; lean_object* v___f_916_; lean_object* v___f_917_; lean_object* v___f_918_; lean_object* v___x_919_; 
v_toApplicative_911_ = lean_ctor_get(v_inst_907_, 0);
lean_inc_ref(v_toApplicative_911_);
v_toBind_912_ = lean_ctor_get(v_inst_907_, 1);
lean_inc(v_toBind_912_);
lean_dec_ref(v_inst_907_);
v_toPure_913_ = lean_ctor_get(v_toApplicative_911_, 1);
lean_inc_n(v_toPure_913_, 2);
lean_dec_ref(v_toApplicative_911_);
v___f_914_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_915_ = lean_box(0);
v___f_916_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_916_, 0, v___x_915_);
lean_closure_set(v___f_916_, 1, v_toPure_913_);
v___f_917_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_917_, 0, v_toPure_913_);
v___f_918_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_918_, 0, v_f_910_);
lean_closure_set(v___f_918_, 1, v_toBind_912_);
lean_closure_set(v___f_918_, 2, v___f_916_);
lean_closure_set(v___f_918_, 3, v___f_917_);
v___x_919_ = lean_apply_6(v_inst_908_, v___f_914_, lean_box(0), lean_box(0), v_it_909_, v___x_915_, v___f_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f(lean_object* v_00_u03b1_920_, lean_object* v_00_u03b2_921_, lean_object* v_00_u03b3_922_, lean_object* v_m_923_, lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_inst_926_, lean_object* v_inst_927_, lean_object* v_it_928_, lean_object* v_f_929_){
_start:
{
lean_object* v_toApplicative_930_; lean_object* v_toBind_931_; lean_object* v_toPure_932_; lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___f_935_; lean_object* v___f_936_; lean_object* v___f_937_; lean_object* v___x_938_; 
v_toApplicative_930_ = lean_ctor_get(v_inst_924_, 0);
lean_inc_ref(v_toApplicative_930_);
v_toBind_931_ = lean_ctor_get(v_inst_924_, 1);
lean_inc(v_toBind_931_);
lean_dec_ref(v_inst_924_);
v_toPure_932_ = lean_ctor_get(v_toApplicative_930_, 1);
lean_inc_n(v_toPure_932_, 2);
lean_dec_ref(v_toApplicative_930_);
v___f_933_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_934_ = lean_box(0);
v___f_935_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_935_, 0, v___x_934_);
lean_closure_set(v___f_935_, 1, v_toPure_932_);
v___f_936_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_936_, 0, v_toPure_932_);
v___f_937_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_937_, 0, v_f_929_);
lean_closure_set(v___f_937_, 1, v_toBind_931_);
lean_closure_set(v___f_937_, 2, v___f_935_);
lean_closure_set(v___f_937_, 3, v___f_936_);
v___x_938_ = lean_apply_6(v_inst_926_, v___f_933_, lean_box(0), lean_box(0), v_it_928_, v___x_934_, v___f_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f___boxed(lean_object* v_00_u03b1_939_, lean_object* v_00_u03b2_940_, lean_object* v_00_u03b3_941_, lean_object* v_m_942_, lean_object* v_inst_943_, lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_inst_946_, lean_object* v_it_947_, lean_object* v_f_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Std_Iter_Total_findSomeM_x3f(v_00_u03b1_939_, v_00_u03b2_940_, v_00_u03b3_941_, v_m_942_, v_inst_943_, v_inst_944_, v_inst_945_, v_inst_946_, v_it_947_, v_f_948_);
lean_dec(v_inst_944_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg___lam__1(lean_object* v_f_950_, lean_object* v___x_951_, lean_object* v_x1_952_, lean_object* v_x2_953_, lean_object* v_x3_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = lean_apply_1(v_f_950_, v_x1_952_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v___x_956_; 
v___x_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_951_);
return v___x_956_;
}
else
{
lean_object* v___x_957_; 
lean_dec(v___x_951_);
v___x_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
return v___x_957_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg___lam__1___boxed(lean_object* v_f_958_, lean_object* v___x_959_, lean_object* v_x1_960_, lean_object* v_x2_961_, lean_object* v_x3_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Std_Iter_findSome_x3f___redArg___lam__1(v_f_958_, v___x_959_, v_x1_960_, v_x2_961_, v_x3_962_);
lean_dec(v_x3_962_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg(lean_object* v_inst_964_, lean_object* v_it_965_, lean_object* v_f_966_){
_start:
{
lean_object* v___f_967_; lean_object* v___x_968_; lean_object* v___f_969_; lean_object* v___x_970_; 
v___f_967_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_968_ = lean_box(0);
v___f_969_ = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_969_, 0, v_f_966_);
lean_closure_set(v___f_969_, 1, v___x_968_);
v___x_970_ = lean_apply_6(v_inst_964_, v___f_967_, lean_box(0), lean_box(0), v_it_965_, v___x_968_, v___f_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f(lean_object* v_00_u03b1_971_, lean_object* v_00_u03b2_972_, lean_object* v_00_u03b3_973_, lean_object* v_inst_974_, lean_object* v_inst_975_, lean_object* v_it_976_, lean_object* v_f_977_){
_start:
{
lean_object* v___f_978_; lean_object* v___x_979_; lean_object* v___f_980_; lean_object* v___x_981_; 
v___f_978_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_979_ = lean_box(0);
v___f_980_ = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_980_, 0, v_f_977_);
lean_closure_set(v___f_980_, 1, v___x_979_);
v___x_981_ = lean_apply_6(v_inst_975_, v___f_978_, lean_box(0), lean_box(0), v_it_976_, v___x_979_, v___f_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___boxed(lean_object* v_00_u03b1_982_, lean_object* v_00_u03b2_983_, lean_object* v_00_u03b3_984_, lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_it_987_, lean_object* v_f_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Std_Iter_findSome_x3f(v_00_u03b1_982_, v_00_u03b2_983_, v_00_u03b3_984_, v_inst_985_, v_inst_986_, v_it_987_, v_f_988_);
lean_dec(v_inst_985_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSome_x3f___redArg(lean_object* v_inst_990_, lean_object* v_it_991_, lean_object* v_f_992_){
_start:
{
lean_object* v___f_993_; lean_object* v___x_994_; lean_object* v___f_995_; lean_object* v___x_996_; 
v___f_993_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_994_ = lean_box(0);
v___f_995_ = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_995_, 0, v_f_992_);
lean_closure_set(v___f_995_, 1, v___x_994_);
v___x_996_ = lean_apply_6(v_inst_990_, v___f_993_, lean_box(0), lean_box(0), v_it_991_, v___x_994_, v___f_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSome_x3f(lean_object* v_00_u03b1_997_, lean_object* v_00_u03b2_998_, lean_object* v_00_u03b3_999_, lean_object* v_inst_1000_, lean_object* v_inst_1001_, lean_object* v_inst_1002_, lean_object* v_it_1003_, lean_object* v_f_1004_){
_start:
{
lean_object* v___f_1005_; lean_object* v___x_1006_; lean_object* v___f_1007_; lean_object* v___x_1008_; 
v___f_1005_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1006_ = lean_box(0);
v___f_1007_ = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1007_, 0, v_f_1004_);
lean_closure_set(v___f_1007_, 1, v___x_1006_);
v___x_1008_ = lean_apply_6(v_inst_1001_, v___f_1005_, lean_box(0), lean_box(0), v_it_1003_, v___x_1006_, v___f_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSome_x3f___boxed(lean_object* v_00_u03b1_1009_, lean_object* v_00_u03b2_1010_, lean_object* v_00_u03b3_1011_, lean_object* v_inst_1012_, lean_object* v_inst_1013_, lean_object* v_inst_1014_, lean_object* v_it_1015_, lean_object* v_f_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Std_Iter_Total_findSome_x3f(v_00_u03b1_1009_, v_00_u03b2_1010_, v_00_u03b3_1011_, v_inst_1012_, v_inst_1013_, v_inst_1014_, v_it_1015_, v_f_1016_);
lean_dec(v_inst_1012_);
return v_res_1017_;
}
}
lean_object* l_Std_Iter_findM_x3f___redArg___lam__3(lean_object* v_toPure_1018_, lean_object* v___x_1019_, lean_object* v_x1_1020_, uint8_t v_____do__lift_1021_){
_start:
{
if (v_____do__lift_1021_ == 0)
{
lean_object* v___x_1022_; 
lean_dec(v_x1_1020_);
v___x_1022_ = lean_apply_2(v_toPure_1018_, lean_box(0), v___x_1019_);
return v___x_1022_;
}
else
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_dec(v___x_1019_);
v___x_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1023_, 0, v_x1_1020_);
v___x_1024_ = lean_apply_2(v_toPure_1018_, lean_box(0), v___x_1023_);
return v___x_1024_;
}
}
}
LEAN_EXPORT void l_Std_Iter_findM_x3f___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_1018_ = stack[0].m_obj;
lean_object* v___x_1019_ = stack[1].m_obj;
lean_object* v_x1_1020_ = stack[2].m_obj;
uint8_t v_____do__lift_1021_ = stack[3].m_num;
lean_object* v_res_1025_;
v_res_1025_ = l_Std_Iter_findM_x3f___redArg___lam__3(v_toPure_1018_, v___x_1019_, v_x1_1020_, v_____do__lift_1021_);
stack->m_obj
 = v_res_1025_;
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__3___boxed(lean_object* v_toPure_1026_, lean_object* v___x_1027_, lean_object* v_x1_1028_, lean_object* v_____do__lift_1029_){
_start:
{
uint8_t v_____do__lift_169__boxed_1030_; lean_object* v_res_1031_; 
v_____do__lift_169__boxed_1030_ = lean_unbox(v_____do__lift_1029_);
v_res_1031_ = l_Std_Iter_findM_x3f___redArg___lam__3(v_toPure_1026_, v___x_1027_, v_x1_1028_, v_____do__lift_169__boxed_1030_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__0(lean_object* v_toPure_1032_, lean_object* v___x_1033_, lean_object* v_f_1034_, lean_object* v_toBind_1035_, lean_object* v___f_1036_, lean_object* v___f_1037_, lean_object* v_x1_1038_, lean_object* v_x2_1039_, lean_object* v_x3_1040_){
_start:
{
lean_object* v___f_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_inc(v_x1_1038_);
v___f_1041_ = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_1041_, 0, v_toPure_1032_);
lean_closure_set(v___f_1041_, 1, v___x_1033_);
lean_closure_set(v___f_1041_, 2, v_x1_1038_);
v___x_1042_ = lean_apply_1(v_f_1034_, v_x1_1038_);
lean_inc_n(v_toBind_1035_, 2);
v___x_1043_ = lean_apply_4(v_toBind_1035_, lean_box(0), lean_box(0), v___x_1042_, v___f_1041_);
v___x_1044_ = lean_apply_4(v_toBind_1035_, lean_box(0), lean_box(0), v___x_1043_, v___f_1036_);
v___x_1045_ = lean_apply_4(v_toBind_1035_, lean_box(0), lean_box(0), v___x_1044_, v___f_1037_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_1046_, lean_object* v___x_1047_, lean_object* v_f_1048_, lean_object* v_toBind_1049_, lean_object* v___f_1050_, lean_object* v___f_1051_, lean_object* v_x1_1052_, lean_object* v_x2_1053_, lean_object* v_x3_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Std_Iter_findM_x3f___redArg___lam__0(v_toPure_1046_, v___x_1047_, v_f_1048_, v_toBind_1049_, v___f_1050_, v___f_1051_, v_x1_1052_, v_x2_1053_, v_x3_1054_);
lean_dec(v_x3_1054_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg(lean_object* v_inst_1056_, lean_object* v_inst_1057_, lean_object* v_it_1058_, lean_object* v_f_1059_){
_start:
{
lean_object* v_toApplicative_1060_; lean_object* v_toBind_1061_; lean_object* v_toPure_1062_; lean_object* v___f_1063_; lean_object* v___f_1064_; lean_object* v___x_1065_; lean_object* v___f_1066_; lean_object* v___f_1067_; lean_object* v___x_1068_; 
v_toApplicative_1060_ = lean_ctor_get(v_inst_1056_, 0);
lean_inc_ref(v_toApplicative_1060_);
v_toBind_1061_ = lean_ctor_get(v_inst_1056_, 1);
lean_inc(v_toBind_1061_);
lean_dec_ref(v_inst_1056_);
v_toPure_1062_ = lean_ctor_get(v_toApplicative_1060_, 1);
lean_inc_n(v_toPure_1062_, 3);
lean_dec_ref(v_toApplicative_1060_);
v___f_1063_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_1064_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1064_, 0, v_toPure_1062_);
v___x_1065_ = lean_box(0);
v___f_1066_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1066_, 0, v___x_1065_);
lean_closure_set(v___f_1066_, 1, v_toPure_1062_);
v___f_1067_ = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1067_, 0, v_toPure_1062_);
lean_closure_set(v___f_1067_, 1, v___x_1065_);
lean_closure_set(v___f_1067_, 2, v_f_1059_);
lean_closure_set(v___f_1067_, 3, v_toBind_1061_);
lean_closure_set(v___f_1067_, 4, v___f_1066_);
lean_closure_set(v___f_1067_, 5, v___f_1064_);
v___x_1068_ = lean_apply_6(v_inst_1057_, v___f_1063_, lean_box(0), lean_box(0), v_it_1058_, v___x_1065_, v___f_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f(lean_object* v_00_u03b1_1069_, lean_object* v_00_u03b2_1070_, lean_object* v_m_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_inst_1074_, lean_object* v_it_1075_, lean_object* v_f_1076_){
_start:
{
lean_object* v_toApplicative_1077_; lean_object* v_toBind_1078_; lean_object* v_toPure_1079_; lean_object* v___f_1080_; lean_object* v___f_1081_; lean_object* v___x_1082_; lean_object* v___f_1083_; lean_object* v___f_1084_; lean_object* v___x_1085_; 
v_toApplicative_1077_ = lean_ctor_get(v_inst_1072_, 0);
lean_inc_ref(v_toApplicative_1077_);
v_toBind_1078_ = lean_ctor_get(v_inst_1072_, 1);
lean_inc(v_toBind_1078_);
lean_dec_ref(v_inst_1072_);
v_toPure_1079_ = lean_ctor_get(v_toApplicative_1077_, 1);
lean_inc_n(v_toPure_1079_, 3);
lean_dec_ref(v_toApplicative_1077_);
v___f_1080_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_1081_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1081_, 0, v_toPure_1079_);
v___x_1082_ = lean_box(0);
v___f_1083_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1083_, 0, v___x_1082_);
lean_closure_set(v___f_1083_, 1, v_toPure_1079_);
v___f_1084_ = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1084_, 0, v_toPure_1079_);
lean_closure_set(v___f_1084_, 1, v___x_1082_);
lean_closure_set(v___f_1084_, 2, v_f_1076_);
lean_closure_set(v___f_1084_, 3, v_toBind_1078_);
lean_closure_set(v___f_1084_, 4, v___f_1083_);
lean_closure_set(v___f_1084_, 5, v___f_1081_);
v___x_1085_ = lean_apply_6(v_inst_1074_, v___f_1080_, lean_box(0), lean_box(0), v_it_1075_, v___x_1082_, v___f_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___boxed(lean_object* v_00_u03b1_1086_, lean_object* v_00_u03b2_1087_, lean_object* v_m_1088_, lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v_inst_1091_, lean_object* v_it_1092_, lean_object* v_f_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Std_Iter_findM_x3f(v_00_u03b1_1086_, v_00_u03b2_1087_, v_m_1088_, v_inst_1089_, v_inst_1090_, v_inst_1091_, v_it_1092_, v_f_1093_);
lean_dec(v_inst_1090_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f___redArg(lean_object* v_inst_1095_, lean_object* v_inst_1096_, lean_object* v_it_1097_, lean_object* v_f_1098_){
_start:
{
lean_object* v_toApplicative_1099_; lean_object* v_toBind_1100_; lean_object* v_toPure_1101_; lean_object* v___f_1102_; lean_object* v___f_1103_; lean_object* v___x_1104_; lean_object* v___f_1105_; lean_object* v___f_1106_; lean_object* v___x_1107_; 
v_toApplicative_1099_ = lean_ctor_get(v_inst_1095_, 0);
lean_inc_ref(v_toApplicative_1099_);
v_toBind_1100_ = lean_ctor_get(v_inst_1095_, 1);
lean_inc(v_toBind_1100_);
lean_dec_ref(v_inst_1095_);
v_toPure_1101_ = lean_ctor_get(v_toApplicative_1099_, 1);
lean_inc_n(v_toPure_1101_, 3);
lean_dec_ref(v_toApplicative_1099_);
v___f_1102_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_1103_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1103_, 0, v_toPure_1101_);
v___x_1104_ = lean_box(0);
v___f_1105_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1105_, 0, v___x_1104_);
lean_closure_set(v___f_1105_, 1, v_toPure_1101_);
v___f_1106_ = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1106_, 0, v_toPure_1101_);
lean_closure_set(v___f_1106_, 1, v___x_1104_);
lean_closure_set(v___f_1106_, 2, v_f_1098_);
lean_closure_set(v___f_1106_, 3, v_toBind_1100_);
lean_closure_set(v___f_1106_, 4, v___f_1105_);
lean_closure_set(v___f_1106_, 5, v___f_1103_);
v___x_1107_ = lean_apply_6(v_inst_1096_, v___f_1102_, lean_box(0), lean_box(0), v_it_1097_, v___x_1104_, v___f_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f(lean_object* v_00_u03b1_1108_, lean_object* v_00_u03b2_1109_, lean_object* v_m_1110_, lean_object* v_inst_1111_, lean_object* v_inst_1112_, lean_object* v_inst_1113_, lean_object* v_inst_1114_, lean_object* v_it_1115_, lean_object* v_f_1116_){
_start:
{
lean_object* v_toApplicative_1117_; lean_object* v_toBind_1118_; lean_object* v_toPure_1119_; lean_object* v___f_1120_; lean_object* v___f_1121_; lean_object* v___x_1122_; lean_object* v___f_1123_; lean_object* v___f_1124_; lean_object* v___x_1125_; 
v_toApplicative_1117_ = lean_ctor_get(v_inst_1111_, 0);
lean_inc_ref(v_toApplicative_1117_);
v_toBind_1118_ = lean_ctor_get(v_inst_1111_, 1);
lean_inc(v_toBind_1118_);
lean_dec_ref(v_inst_1111_);
v_toPure_1119_ = lean_ctor_get(v_toApplicative_1117_, 1);
lean_inc_n(v_toPure_1119_, 3);
lean_dec_ref(v_toApplicative_1117_);
v___f_1120_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_1121_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1121_, 0, v_toPure_1119_);
v___x_1122_ = lean_box(0);
v___f_1123_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1123_, 0, v___x_1122_);
lean_closure_set(v___f_1123_, 1, v_toPure_1119_);
v___f_1124_ = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1124_, 0, v_toPure_1119_);
lean_closure_set(v___f_1124_, 1, v___x_1122_);
lean_closure_set(v___f_1124_, 2, v_f_1116_);
lean_closure_set(v___f_1124_, 3, v_toBind_1118_);
lean_closure_set(v___f_1124_, 4, v___f_1123_);
lean_closure_set(v___f_1124_, 5, v___f_1121_);
v___x_1125_ = lean_apply_6(v_inst_1113_, v___f_1120_, lean_box(0), lean_box(0), v_it_1115_, v___x_1122_, v___f_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f___boxed(lean_object* v_00_u03b1_1126_, lean_object* v_00_u03b2_1127_, lean_object* v_m_1128_, lean_object* v_inst_1129_, lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_it_1133_, lean_object* v_f_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Std_Iter_Total_findM_x3f(v_00_u03b1_1126_, v_00_u03b2_1127_, v_m_1128_, v_inst_1129_, v_inst_1130_, v_inst_1131_, v_inst_1132_, v_it_1133_, v_f_1134_);
lean_dec(v_inst_1130_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg___lam__1(lean_object* v_f_1136_, lean_object* v___x_1137_, lean_object* v_x1_1138_, lean_object* v_x2_1139_, lean_object* v_x3_1140_){
_start:
{
lean_object* v___x_1141_; uint8_t v___x_1142_; 
lean_inc(v_x1_1138_);
v___x_1141_ = lean_apply_1(v_f_1136_, v_x1_1138_);
v___x_1142_ = lean_unbox(v___x_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; 
lean_dec(v_x1_1138_);
v___x_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1137_);
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec(v___x_1137_);
v___x_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1144_, 0, v_x1_1138_);
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg___lam__1___boxed(lean_object* v_f_1146_, lean_object* v___x_1147_, lean_object* v_x1_1148_, lean_object* v_x2_1149_, lean_object* v_x3_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Std_Iter_find_x3f___redArg___lam__1(v_f_1146_, v___x_1147_, v_x1_1148_, v_x2_1149_, v_x3_1150_);
lean_dec(v_x3_1150_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg(lean_object* v_inst_1152_, lean_object* v_it_1153_, lean_object* v_f_1154_){
_start:
{
lean_object* v___f_1155_; lean_object* v___x_1156_; lean_object* v___f_1157_; lean_object* v___x_1158_; 
v___f_1155_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1156_ = lean_box(0);
v___f_1157_ = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1157_, 0, v_f_1154_);
lean_closure_set(v___f_1157_, 1, v___x_1156_);
v___x_1158_ = lean_apply_6(v_inst_1152_, v___f_1155_, lean_box(0), lean_box(0), v_it_1153_, v___x_1156_, v___f_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f(lean_object* v_00_u03b1_1159_, lean_object* v_00_u03b2_1160_, lean_object* v_inst_1161_, lean_object* v_inst_1162_, lean_object* v_it_1163_, lean_object* v_f_1164_){
_start:
{
lean_object* v___f_1165_; lean_object* v___x_1166_; lean_object* v___f_1167_; lean_object* v___x_1168_; 
v___f_1165_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1166_ = lean_box(0);
v___f_1167_ = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1167_, 0, v_f_1164_);
lean_closure_set(v___f_1167_, 1, v___x_1166_);
v___x_1168_ = lean_apply_6(v_inst_1162_, v___f_1165_, lean_box(0), lean_box(0), v_it_1163_, v___x_1166_, v___f_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___boxed(lean_object* v_00_u03b1_1169_, lean_object* v_00_u03b2_1170_, lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_it_1173_, lean_object* v_f_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Std_Iter_find_x3f(v_00_u03b1_1169_, v_00_u03b2_1170_, v_inst_1171_, v_inst_1172_, v_it_1173_, v_f_1174_);
lean_dec(v_inst_1171_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_find_x3f___redArg(lean_object* v_inst_1176_, lean_object* v_it_1177_, lean_object* v_f_1178_){
_start:
{
lean_object* v___f_1179_; lean_object* v___x_1180_; lean_object* v___f_1181_; lean_object* v___x_1182_; 
v___f_1179_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1180_ = lean_box(0);
v___f_1181_ = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1181_, 0, v_f_1178_);
lean_closure_set(v___f_1181_, 1, v___x_1180_);
v___x_1182_ = lean_apply_6(v_inst_1176_, v___f_1179_, lean_box(0), lean_box(0), v_it_1177_, v___x_1180_, v___f_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_find_x3f(lean_object* v_00_u03b1_1183_, lean_object* v_00_u03b2_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_it_1188_, lean_object* v_f_1189_){
_start:
{
lean_object* v___f_1190_; lean_object* v___x_1191_; lean_object* v___f_1192_; lean_object* v___x_1193_; 
v___f_1190_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1191_ = lean_box(0);
v___f_1192_ = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1192_, 0, v_f_1189_);
lean_closure_set(v___f_1192_, 1, v___x_1191_);
v___x_1193_ = lean_apply_6(v_inst_1186_, v___f_1190_, lean_box(0), lean_box(0), v_it_1188_, v___x_1191_, v___f_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_find_x3f___boxed(lean_object* v_00_u03b1_1194_, lean_object* v_00_u03b2_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_inst_1198_, lean_object* v_it_1199_, lean_object* v_f_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Std_Iter_Total_find_x3f(v_00_u03b1_1194_, v_00_u03b2_1195_, v_inst_1196_, v_inst_1197_, v_inst_1198_, v_it_1199_, v_f_1200_);
lean_dec(v_inst_1196_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___redArg___lam__0(lean_object* v_x_1202_, lean_object* v_x_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_apply_1(v___y_1204_, v___y_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___redArg___lam__1(lean_object* v_b_1207_, lean_object* v_x_1208_, lean_object* v_x_1209_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1210_, 0, v_b_1207_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___redArg___lam__1___boxed(lean_object* v_b_1212_, lean_object* v_x_1213_, lean_object* v_x_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Std_Iter_first_x3f___redArg___lam__1(v_b_1212_, v_x_1213_, v_x_1214_);
lean_dec(v_x_1214_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___redArg(lean_object* v_inst_1218_, lean_object* v_it_1219_){
_start:
{
lean_object* v___f_1220_; lean_object* v___f_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___f_1220_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1221_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__1));
v___x_1222_ = lean_box(0);
v___x_1223_ = lean_apply_6(v_inst_1218_, v___f_1220_, lean_box(0), lean_box(0), v_it_1219_, v___x_1222_, v___f_1221_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f(lean_object* v_00_u03b1_1224_, lean_object* v_00_u03b2_1225_, lean_object* v_inst_1226_, lean_object* v_inst_1227_, lean_object* v_it_1228_){
_start:
{
lean_object* v___f_1229_; lean_object* v___f_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___f_1229_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1230_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__1));
v___x_1231_ = lean_box(0);
v___x_1232_ = lean_apply_6(v_inst_1227_, v___f_1229_, lean_box(0), lean_box(0), v_it_1228_, v___x_1231_, v___f_1230_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___boxed(lean_object* v_00_u03b1_1233_, lean_object* v_00_u03b2_1234_, lean_object* v_inst_1235_, lean_object* v_inst_1236_, lean_object* v_it_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Std_Iter_first_x3f(v_00_u03b1_1233_, v_00_u03b2_1234_, v_inst_1235_, v_inst_1236_, v_it_1237_);
lean_dec(v_inst_1235_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_first_x3f___redArg(lean_object* v_inst_1239_, lean_object* v_it_1240_){
_start:
{
lean_object* v___f_1241_; lean_object* v___f_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___f_1241_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1242_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__1));
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_apply_6(v_inst_1239_, v___f_1241_, lean_box(0), lean_box(0), v_it_1240_, v___x_1243_, v___f_1242_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_first_x3f(lean_object* v_00_u03b1_1245_, lean_object* v_00_u03b2_1246_, lean_object* v_inst_1247_, lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_it_1250_){
_start:
{
lean_object* v___f_1251_; lean_object* v___f_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___f_1251_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1252_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__1));
v___x_1253_ = lean_box(0);
v___x_1254_ = lean_apply_6(v_inst_1248_, v___f_1251_, lean_box(0), lean_box(0), v_it_1250_, v___x_1253_, v___f_1252_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_first_x3f___boxed(lean_object* v_00_u03b1_1255_, lean_object* v_00_u03b2_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_it_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Std_Iter_Total_first_x3f(v_00_u03b1_1255_, v_00_u03b2_1256_, v_inst_1257_, v_inst_1258_, v_inst_1259_, v_it_1260_);
lean_dec(v_inst_1257_);
return v_res_1261_;
}
}
lean_object* l_Std_Iter_isEmpty___redArg___lam__1(lean_object* v_x_1265_, lean_object* v_x_1266_, uint8_t v_x_1267_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = ((lean_object*)(l_Std_Iter_isEmpty___redArg___lam__1___closed__0));
return v___x_1268_;
}
}
LEAN_EXPORT void l_Std_Iter_isEmpty___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1265_ = stack[0].m_obj;
uint8_t v_x_1267_ = stack[2].m_num;
lean_object* v_res_1269_;
v_res_1269_ = l_Std_Iter_isEmpty___redArg___lam__1(v_x_1265_, lean_box(0), v_x_1267_);
stack->m_obj
 = v_res_1269_;
}
LEAN_EXPORT lean_object* l_Std_Iter_isEmpty___redArg___lam__1___boxed(lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_){
_start:
{
uint8_t v_x_151__boxed_1273_; lean_object* v_res_1274_; 
v_x_151__boxed_1273_ = lean_unbox(v_x_1272_);
v_res_1274_ = l_Std_Iter_isEmpty___redArg___lam__1(v_x_1270_, v_x_1271_, v_x_151__boxed_1273_);
lean_dec(v_x_1270_);
return v_res_1274_;
}
}
uint8_t l_Std_Iter_isEmpty___redArg(lean_object* v_inst_1276_, lean_object* v_it_1277_){
_start:
{
lean_object* v___f_1278_; lean_object* v___f_1279_; uint8_t v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___f_1278_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1279_ = ((lean_object*)(l_Std_Iter_isEmpty___redArg___closed__0));
v___x_1280_ = 1;
v___x_1281_ = lean_box(v___x_1280_);
v___x_1282_ = lean_apply_6(v_inst_1276_, v___f_1278_, lean_box(0), lean_box(0), v_it_1277_, v___x_1281_, v___f_1279_);
v___x_1283_ = lean_unbox(v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT void l_Std_Iter_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1276_ = stack[0].m_obj;
lean_object* v_it_1277_ = stack[1].m_obj;
uint8_t v_res_1284_;
v_res_1284_ = l_Std_Iter_isEmpty___redArg(v_inst_1276_, v_it_1277_);
stack->m_num = v_res_1284_;
}
LEAN_EXPORT lean_object* l_Std_Iter_isEmpty___redArg___boxed(lean_object* v_inst_1285_, lean_object* v_it_1286_){
_start:
{
uint8_t v_res_1287_; lean_object* v_r_1288_; 
v_res_1287_ = l_Std_Iter_isEmpty___redArg(v_inst_1285_, v_it_1286_);
v_r_1288_ = lean_box(v_res_1287_);
return v_r_1288_;
}
}
uint8_t l_Std_Iter_isEmpty(lean_object* v_00_u03b1_1289_, lean_object* v_00_u03b2_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_it_1293_){
_start:
{
lean_object* v___f_1294_; lean_object* v___f_1295_; uint8_t v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___f_1294_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1295_ = ((lean_object*)(l_Std_Iter_isEmpty___redArg___closed__0));
v___x_1296_ = 1;
v___x_1297_ = lean_box(v___x_1296_);
v___x_1298_ = lean_apply_6(v_inst_1292_, v___f_1294_, lean_box(0), lean_box(0), v_it_1293_, v___x_1297_, v___f_1295_);
v___x_1299_ = lean_unbox(v___x_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT void l_Std_Iter_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1291_ = stack[2].m_obj;
lean_object* v_inst_1292_ = stack[3].m_obj;
lean_object* v_it_1293_ = stack[4].m_obj;
uint8_t v_res_1300_;
v_res_1300_ = l_Std_Iter_isEmpty(lean_box(0), lean_box(0), v_inst_1291_, v_inst_1292_, v_it_1293_);
stack->m_num = v_res_1300_;
}
LEAN_EXPORT lean_object* l_Std_Iter_isEmpty___boxed(lean_object* v_00_u03b1_1301_, lean_object* v_00_u03b2_1302_, lean_object* v_inst_1303_, lean_object* v_inst_1304_, lean_object* v_it_1305_){
_start:
{
uint8_t v_res_1306_; lean_object* v_r_1307_; 
v_res_1306_ = l_Std_Iter_isEmpty(v_00_u03b1_1301_, v_00_u03b2_1302_, v_inst_1303_, v_inst_1304_, v_it_1305_);
lean_dec(v_inst_1303_);
v_r_1307_ = lean_box(v_res_1306_);
return v_r_1307_;
}
}
uint8_t l_Std_Iter_Total_isEmpty___redArg(lean_object* v_inst_1308_, lean_object* v_it_1309_){
_start:
{
lean_object* v___f_1310_; lean_object* v___f_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___f_1310_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1311_ = ((lean_object*)(l_Std_Iter_isEmpty___redArg___closed__0));
v___x_1312_ = 1;
v___x_1313_ = lean_box(v___x_1312_);
v___x_1314_ = lean_apply_6(v_inst_1308_, v___f_1310_, lean_box(0), lean_box(0), v_it_1309_, v___x_1313_, v___f_1311_);
v___x_1315_ = lean_unbox(v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT void l_Std_Iter_Total_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1308_ = stack[0].m_obj;
lean_object* v_it_1309_ = stack[1].m_obj;
uint8_t v_res_1316_;
v_res_1316_ = l_Std_Iter_Total_isEmpty___redArg(v_inst_1308_, v_it_1309_);
stack->m_num = v_res_1316_;
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_isEmpty___redArg___boxed(lean_object* v_inst_1317_, lean_object* v_it_1318_){
_start:
{
uint8_t v_res_1319_; lean_object* v_r_1320_; 
v_res_1319_ = l_Std_Iter_Total_isEmpty___redArg(v_inst_1317_, v_it_1318_);
v_r_1320_ = lean_box(v_res_1319_);
return v_r_1320_;
}
}
uint8_t l_Std_Iter_Total_isEmpty(lean_object* v_00_u03b1_1321_, lean_object* v_00_u03b2_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_it_1326_){
_start:
{
lean_object* v___f_1327_; lean_object* v___f_1328_; uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___f_1327_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1328_ = ((lean_object*)(l_Std_Iter_isEmpty___redArg___closed__0));
v___x_1329_ = 1;
v___x_1330_ = lean_box(v___x_1329_);
v___x_1331_ = lean_apply_6(v_inst_1324_, v___f_1327_, lean_box(0), lean_box(0), v_it_1326_, v___x_1330_, v___f_1328_);
v___x_1332_ = lean_unbox(v___x_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT void l_Std_Iter_Total_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1323_ = stack[2].m_obj;
lean_object* v_inst_1324_ = stack[3].m_obj;
lean_object* v_it_1326_ = stack[5].m_obj;
uint8_t v_res_1333_;
v_res_1333_ = l_Std_Iter_Total_isEmpty(lean_box(0), lean_box(0), v_inst_1323_, v_inst_1324_, lean_box(0), v_it_1326_);
stack->m_num = v_res_1333_;
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_isEmpty___boxed(lean_object* v_00_u03b1_1334_, lean_object* v_00_u03b2_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_it_1339_){
_start:
{
uint8_t v_res_1340_; lean_object* v_r_1341_; 
v_res_1340_ = l_Std_Iter_Total_isEmpty(v_00_u03b1_1334_, v_00_u03b2_1335_, v_inst_1336_, v_inst_1337_, v_inst_1338_, v_it_1339_);
lean_dec(v_inst_1336_);
v_r_1341_ = lean_box(v_res_1340_);
return v_r_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_length___redArg___lam__0(lean_object* v_x_1342_, lean_object* v_x_1343_, lean_object* v_f_1344_, lean_object* v_x_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_apply_1(v_f_1344_, v_x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_length___redArg___lam__1(lean_object* v_x1_1347_, lean_object* v_x2_1348_, lean_object* v_x3_1349_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = lean_unsigned_to_nat(1u);
v___x_1351_ = lean_nat_add(v_x3_1349_, v___x_1350_);
v___x_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_length___redArg___lam__1___boxed(lean_object* v_x1_1353_, lean_object* v_x2_1354_, lean_object* v_x3_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Std_Iter_length___redArg___lam__1(v_x1_1353_, v_x2_1354_, v_x3_1355_);
lean_dec(v_x3_1355_);
lean_dec(v_x1_1353_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_length___redArg(lean_object* v_inst_1359_, lean_object* v_it_1360_){
_start:
{
lean_object* v___f_1361_; lean_object* v___f_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___f_1361_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__0));
v___f_1362_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__1));
v___x_1363_ = lean_unsigned_to_nat(0u);
v___x_1364_ = lean_apply_6(v_inst_1359_, v___f_1361_, lean_box(0), lean_box(0), v_it_1360_, v___x_1363_, v___f_1362_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_length(lean_object* v_00_u03b1_1365_, lean_object* v_00_u03b2_1366_, lean_object* v_inst_1367_, lean_object* v_inst_1368_, lean_object* v_it_1369_){
_start:
{
lean_object* v___f_1370_; lean_object* v___f_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___f_1370_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__0));
v___f_1371_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__1));
v___x_1372_ = lean_unsigned_to_nat(0u);
v___x_1373_ = lean_apply_6(v_inst_1368_, v___f_1370_, lean_box(0), lean_box(0), v_it_1369_, v___x_1372_, v___f_1371_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_length___boxed(lean_object* v_00_u03b1_1374_, lean_object* v_00_u03b2_1375_, lean_object* v_inst_1376_, lean_object* v_inst_1377_, lean_object* v_it_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Std_Iter_length(v_00_u03b1_1374_, v_00_u03b2_1375_, v_inst_1376_, v_inst_1377_, v_it_1378_);
lean_dec(v_inst_1376_);
return v_res_1379_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Partial(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Total(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Partial(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Partial(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Total(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Partial(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Consumers_Loop(builtin);
}
#ifdef __cplusplus
}
#endif
