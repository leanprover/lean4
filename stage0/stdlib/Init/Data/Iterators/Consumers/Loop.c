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
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__1(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__0(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg___lam__1(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__1(uint8_t v___x_413_, lean_object* v_toPure_414_, uint8_t v_____do__lift_415_){
_start:
{
if (v_____do__lift_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_box(v___x_413_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
v___x_418_ = lean_apply_2(v_toPure_414_, lean_box(0), v___x_417_);
return v___x_418_;
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_box(v_____do__lift_415_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
v___x_421_ = lean_apply_2(v_toPure_414_, lean_box(0), v___x_420_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__1___boxed(lean_object* v___x_422_, lean_object* v_toPure_423_, lean_object* v_____do__lift_424_){
_start:
{
uint8_t v___x_230__boxed_425_; uint8_t v_____do__lift_231__boxed_426_; lean_object* v_res_427_; 
v___x_230__boxed_425_ = lean_unbox(v___x_422_);
v_____do__lift_231__boxed_426_ = lean_unbox(v_____do__lift_424_);
v_res_427_ = l_Std_Iter_anyM___redArg___lam__1(v___x_230__boxed_425_, v_toPure_423_, v_____do__lift_231__boxed_426_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__0(lean_object* v_toPure_428_, lean_object* v_____do__lift_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = lean_apply_2(v_toPure_428_, lean_box(0), v_____do__lift_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__2(lean_object* v_p_431_, lean_object* v_toBind_432_, lean_object* v___f_433_, lean_object* v___f_434_, lean_object* v_x1_435_, lean_object* v_x2_436_, uint8_t v_x3_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_apply_1(v_p_431_, v_x1_435_);
lean_inc(v_toBind_432_);
v___x_439_ = lean_apply_4(v_toBind_432_, lean_box(0), lean_box(0), v___x_438_, v___f_433_);
v___x_440_ = lean_apply_4(v_toBind_432_, lean_box(0), lean_box(0), v___x_439_, v___f_434_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__2___boxed(lean_object* v_p_441_, lean_object* v_toBind_442_, lean_object* v___f_443_, lean_object* v___f_444_, lean_object* v_x1_445_, lean_object* v_x2_446_, lean_object* v_x3_447_){
_start:
{
uint8_t v_x3_256__boxed_448_; lean_object* v_res_449_; 
v_x3_256__boxed_448_ = lean_unbox(v_x3_447_);
v_res_449_ = l_Std_Iter_anyM___redArg___lam__2(v_p_441_, v_toBind_442_, v___f_443_, v___f_444_, v_x1_445_, v_x2_446_, v_x3_256__boxed_448_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg(lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_p_452_, lean_object* v_it_453_){
_start:
{
lean_object* v_toApplicative_454_; lean_object* v_toBind_455_; lean_object* v_toPure_456_; lean_object* v___f_457_; uint8_t v___x_458_; lean_object* v___x_459_; lean_object* v___f_460_; lean_object* v___f_461_; lean_object* v___f_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_toApplicative_454_ = lean_ctor_get(v_inst_450_, 0);
lean_inc_ref(v_toApplicative_454_);
v_toBind_455_ = lean_ctor_get(v_inst_450_, 1);
lean_inc(v_toBind_455_);
lean_dec_ref(v_inst_450_);
v_toPure_456_ = lean_ctor_get(v_toApplicative_454_, 1);
lean_inc_n(v_toPure_456_, 2);
lean_dec_ref(v_toApplicative_454_);
v___f_457_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_458_ = 0;
v___x_459_ = lean_box(v___x_458_);
v___f_460_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_460_, 0, v___x_459_);
lean_closure_set(v___f_460_, 1, v_toPure_456_);
v___f_461_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_461_, 0, v_toPure_456_);
v___f_462_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_462_, 0, v_p_452_);
lean_closure_set(v___f_462_, 1, v_toBind_455_);
lean_closure_set(v___f_462_, 2, v___f_460_);
lean_closure_set(v___f_462_, 3, v___f_461_);
v___x_463_ = lean_box(v___x_458_);
v___x_464_ = lean_apply_6(v_inst_451_, v___f_457_, lean_box(0), lean_box(0), v_it_453_, v___x_463_, v___f_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM(lean_object* v_00_u03b1_465_, lean_object* v_00_u03b2_466_, lean_object* v_m_467_, lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_p_471_, lean_object* v_it_472_){
_start:
{
lean_object* v_toApplicative_473_; lean_object* v_toBind_474_; lean_object* v_toPure_475_; lean_object* v___f_476_; uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___f_479_; lean_object* v___f_480_; lean_object* v___f_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_toApplicative_473_ = lean_ctor_get(v_inst_468_, 0);
lean_inc_ref(v_toApplicative_473_);
v_toBind_474_ = lean_ctor_get(v_inst_468_, 1);
lean_inc(v_toBind_474_);
lean_dec_ref(v_inst_468_);
v_toPure_475_ = lean_ctor_get(v_toApplicative_473_, 1);
lean_inc_n(v_toPure_475_, 2);
lean_dec_ref(v_toApplicative_473_);
v___f_476_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_477_ = 0;
v___x_478_ = lean_box(v___x_477_);
v___f_479_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_479_, 0, v___x_478_);
lean_closure_set(v___f_479_, 1, v_toPure_475_);
v___f_480_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_480_, 0, v_toPure_475_);
v___f_481_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_481_, 0, v_p_471_);
lean_closure_set(v___f_481_, 1, v_toBind_474_);
lean_closure_set(v___f_481_, 2, v___f_479_);
lean_closure_set(v___f_481_, 3, v___f_480_);
v___x_482_ = lean_box(v___x_477_);
v___x_483_ = lean_apply_6(v_inst_470_, v___f_476_, lean_box(0), lean_box(0), v_it_472_, v___x_482_, v___f_481_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___boxed(lean_object* v_00_u03b1_484_, lean_object* v_00_u03b2_485_, lean_object* v_m_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_p_490_, lean_object* v_it_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_Iter_anyM(v_00_u03b1_484_, v_00_u03b2_485_, v_m_486_, v_inst_487_, v_inst_488_, v_inst_489_, v_p_490_, v_it_491_);
lean_dec(v_inst_488_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_anyM___redArg(lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_p_495_, lean_object* v_it_496_){
_start:
{
lean_object* v_toApplicative_497_; lean_object* v_toBind_498_; lean_object* v_toPure_499_; lean_object* v___f_500_; uint8_t v___x_501_; lean_object* v___x_502_; lean_object* v___f_503_; lean_object* v___f_504_; lean_object* v___f_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_toApplicative_497_ = lean_ctor_get(v_inst_493_, 0);
lean_inc_ref(v_toApplicative_497_);
v_toBind_498_ = lean_ctor_get(v_inst_493_, 1);
lean_inc(v_toBind_498_);
lean_dec_ref(v_inst_493_);
v_toPure_499_ = lean_ctor_get(v_toApplicative_497_, 1);
lean_inc_n(v_toPure_499_, 2);
lean_dec_ref(v_toApplicative_497_);
v___f_500_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_501_ = 0;
v___x_502_ = lean_box(v___x_501_);
v___f_503_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_503_, 0, v___x_502_);
lean_closure_set(v___f_503_, 1, v_toPure_499_);
v___f_504_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_504_, 0, v_toPure_499_);
v___f_505_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_505_, 0, v_p_495_);
lean_closure_set(v___f_505_, 1, v_toBind_498_);
lean_closure_set(v___f_505_, 2, v___f_503_);
lean_closure_set(v___f_505_, 3, v___f_504_);
v___x_506_ = lean_box(v___x_501_);
v___x_507_ = lean_apply_6(v_inst_494_, v___f_500_, lean_box(0), lean_box(0), v_it_496_, v___x_506_, v___f_505_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_anyM(lean_object* v_00_u03b1_508_, lean_object* v_00_u03b2_509_, lean_object* v_m_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_p_515_, lean_object* v_it_516_){
_start:
{
lean_object* v_toApplicative_517_; lean_object* v_toBind_518_; lean_object* v_toPure_519_; lean_object* v___f_520_; uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___f_523_; lean_object* v___f_524_; lean_object* v___f_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v_toApplicative_517_ = lean_ctor_get(v_inst_511_, 0);
lean_inc_ref(v_toApplicative_517_);
v_toBind_518_ = lean_ctor_get(v_inst_511_, 1);
lean_inc(v_toBind_518_);
lean_dec_ref(v_inst_511_);
v_toPure_519_ = lean_ctor_get(v_toApplicative_517_, 1);
lean_inc_n(v_toPure_519_, 2);
lean_dec_ref(v_toApplicative_517_);
v___f_520_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_521_ = 0;
v___x_522_ = lean_box(v___x_521_);
v___f_523_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_523_, 0, v___x_522_);
lean_closure_set(v___f_523_, 1, v_toPure_519_);
v___f_524_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_524_, 0, v_toPure_519_);
v___f_525_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_525_, 0, v_p_515_);
lean_closure_set(v___f_525_, 1, v_toBind_518_);
lean_closure_set(v___f_525_, 2, v___f_523_);
lean_closure_set(v___f_525_, 3, v___f_524_);
v___x_526_ = lean_box(v___x_521_);
v___x_527_ = lean_apply_6(v_inst_513_, v___f_520_, lean_box(0), lean_box(0), v_it_516_, v___x_526_, v___f_525_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_anyM___boxed(lean_object* v_00_u03b1_528_, lean_object* v_00_u03b2_529_, lean_object* v_m_530_, lean_object* v_inst_531_, lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_inst_534_, lean_object* v_p_535_, lean_object* v_it_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_Iter_Total_anyM(v_00_u03b1_528_, v_00_u03b2_529_, v_m_530_, v_inst_531_, v_inst_532_, v_inst_533_, v_inst_534_, v_p_535_, v_it_536_);
lean_dec(v_inst_532_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_any___redArg___lam__1(lean_object* v_p_538_, uint8_t v___x_539_, lean_object* v_x1_540_, lean_object* v_x2_541_, uint8_t v_x3_542_){
_start:
{
lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_543_ = lean_apply_1(v_p_538_, v_x1_540_);
v___x_544_ = lean_unbox(v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_box(v___x_539_);
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
else
{
lean_object* v___x_547_; 
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_543_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_any___redArg___lam__1___boxed(lean_object* v_p_548_, lean_object* v___x_549_, lean_object* v_x1_550_, lean_object* v_x2_551_, lean_object* v_x3_552_){
_start:
{
uint8_t v___x_280__boxed_553_; uint8_t v_x3_283__boxed_554_; lean_object* v_res_555_; 
v___x_280__boxed_553_ = lean_unbox(v___x_549_);
v_x3_283__boxed_554_ = lean_unbox(v_x3_552_);
v_res_555_ = l_Std_Iter_any___redArg___lam__1(v_p_548_, v___x_280__boxed_553_, v_x1_550_, v_x2_551_, v_x3_283__boxed_554_);
return v_res_555_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_any___redArg(lean_object* v_inst_556_, lean_object* v_p_557_, lean_object* v_it_558_){
_start:
{
lean_object* v___f_559_; uint8_t v___x_560_; lean_object* v___x_561_; lean_object* v___f_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___f_559_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_560_ = 0;
v___x_561_ = lean_box(v___x_560_);
v___f_562_ = lean_alloc_closure((void*)(l_Std_Iter_any___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_562_, 0, v_p_557_);
lean_closure_set(v___f_562_, 1, v___x_561_);
v___x_563_ = lean_box(v___x_560_);
v___x_564_ = lean_apply_6(v_inst_556_, v___f_559_, lean_box(0), lean_box(0), v_it_558_, v___x_563_, v___f_562_);
v___x_565_ = lean_unbox(v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_any___redArg___boxed(lean_object* v_inst_566_, lean_object* v_p_567_, lean_object* v_it_568_){
_start:
{
uint8_t v_res_569_; lean_object* v_r_570_; 
v_res_569_ = l_Std_Iter_any___redArg(v_inst_566_, v_p_567_, v_it_568_);
v_r_570_ = lean_box(v_res_569_);
return v_r_570_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_any(lean_object* v_00_u03b1_571_, lean_object* v_00_u03b2_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_p_575_, lean_object* v_it_576_){
_start:
{
lean_object* v___f_577_; uint8_t v___x_578_; lean_object* v___x_579_; lean_object* v___f_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___f_577_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_578_ = 0;
v___x_579_ = lean_box(v___x_578_);
v___f_580_ = lean_alloc_closure((void*)(l_Std_Iter_any___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_580_, 0, v_p_575_);
lean_closure_set(v___f_580_, 1, v___x_579_);
v___x_581_ = lean_box(v___x_578_);
v___x_582_ = lean_apply_6(v_inst_574_, v___f_577_, lean_box(0), lean_box(0), v_it_576_, v___x_581_, v___f_580_);
v___x_583_ = lean_unbox(v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_any___boxed(lean_object* v_00_u03b1_584_, lean_object* v_00_u03b2_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_p_588_, lean_object* v_it_589_){
_start:
{
uint8_t v_res_590_; lean_object* v_r_591_; 
v_res_590_ = l_Std_Iter_any(v_00_u03b1_584_, v_00_u03b2_585_, v_inst_586_, v_inst_587_, v_p_588_, v_it_589_);
lean_dec(v_inst_586_);
v_r_591_ = lean_box(v_res_590_);
return v_r_591_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_Total_any___redArg(lean_object* v_inst_592_, lean_object* v_p_593_, lean_object* v_it_594_){
_start:
{
lean_object* v___f_595_; uint8_t v___x_596_; lean_object* v___x_597_; lean_object* v___f_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v___f_595_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_596_ = 0;
v___x_597_ = lean_box(v___x_596_);
v___f_598_ = lean_alloc_closure((void*)(l_Std_Iter_any___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_598_, 0, v_p_593_);
lean_closure_set(v___f_598_, 1, v___x_597_);
v___x_599_ = lean_box(v___x_596_);
v___x_600_ = lean_apply_6(v_inst_592_, v___f_595_, lean_box(0), lean_box(0), v_it_594_, v___x_599_, v___f_598_);
v___x_601_ = lean_unbox(v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_any___redArg___boxed(lean_object* v_inst_602_, lean_object* v_p_603_, lean_object* v_it_604_){
_start:
{
uint8_t v_res_605_; lean_object* v_r_606_; 
v_res_605_ = l_Std_Iter_Total_any___redArg(v_inst_602_, v_p_603_, v_it_604_);
v_r_606_ = lean_box(v_res_605_);
return v_r_606_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_Total_any(lean_object* v_00_u03b1_607_, lean_object* v_00_u03b2_608_, lean_object* v_inst_609_, lean_object* v_inst_610_, lean_object* v_inst_611_, lean_object* v_p_612_, lean_object* v_it_613_){
_start:
{
lean_object* v___f_614_; uint8_t v___x_615_; lean_object* v___x_616_; lean_object* v___f_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___f_614_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_615_ = 0;
v___x_616_ = lean_box(v___x_615_);
v___f_617_ = lean_alloc_closure((void*)(l_Std_Iter_any___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_617_, 0, v_p_612_);
lean_closure_set(v___f_617_, 1, v___x_616_);
v___x_618_ = lean_box(v___x_615_);
v___x_619_ = lean_apply_6(v_inst_610_, v___f_614_, lean_box(0), lean_box(0), v_it_613_, v___x_618_, v___f_617_);
v___x_620_ = lean_unbox(v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_any___boxed(lean_object* v_00_u03b1_621_, lean_object* v_00_u03b2_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_p_626_, lean_object* v_it_627_){
_start:
{
uint8_t v_res_628_; lean_object* v_r_629_; 
v_res_628_ = l_Std_Iter_Total_any(v_00_u03b1_621_, v_00_u03b2_622_, v_inst_623_, v_inst_624_, v_inst_625_, v_p_626_, v_it_627_);
lean_dec(v_inst_623_);
v_r_629_ = lean_box(v_res_628_);
return v_r_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg___lam__1(lean_object* v_toPure_630_, uint8_t v___x_631_, uint8_t v_____do__lift_632_){
_start:
{
if (v_____do__lift_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = lean_box(v_____do__lift_632_);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
v___x_635_ = lean_apply_2(v_toPure_630_, lean_box(0), v___x_634_);
return v___x_635_;
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = lean_box(v___x_631_);
v___x_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
v___x_638_ = lean_apply_2(v_toPure_630_, lean_box(0), v___x_637_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg___lam__1___boxed(lean_object* v_toPure_639_, lean_object* v___x_640_, lean_object* v_____do__lift_641_){
_start:
{
uint8_t v___x_232__boxed_642_; uint8_t v_____do__lift_233__boxed_643_; lean_object* v_res_644_; 
v___x_232__boxed_642_ = lean_unbox(v___x_640_);
v_____do__lift_233__boxed_643_ = lean_unbox(v_____do__lift_641_);
v_res_644_ = l_Std_Iter_allM___redArg___lam__1(v_toPure_639_, v___x_232__boxed_642_, v_____do__lift_233__boxed_643_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg(lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_p_647_, lean_object* v_it_648_){
_start:
{
lean_object* v_toApplicative_649_; lean_object* v_toBind_650_; lean_object* v_toPure_651_; lean_object* v___f_652_; uint8_t v___x_653_; lean_object* v___x_654_; lean_object* v___f_655_; lean_object* v___f_656_; lean_object* v___f_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_toApplicative_649_ = lean_ctor_get(v_inst_645_, 0);
lean_inc_ref(v_toApplicative_649_);
v_toBind_650_ = lean_ctor_get(v_inst_645_, 1);
lean_inc(v_toBind_650_);
lean_dec_ref(v_inst_645_);
v_toPure_651_ = lean_ctor_get(v_toApplicative_649_, 1);
lean_inc_n(v_toPure_651_, 2);
lean_dec_ref(v_toApplicative_649_);
v___f_652_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_653_ = 1;
v___x_654_ = lean_box(v___x_653_);
v___f_655_ = lean_alloc_closure((void*)(l_Std_Iter_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_655_, 0, v_toPure_651_);
lean_closure_set(v___f_655_, 1, v___x_654_);
v___f_656_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_656_, 0, v_toPure_651_);
v___f_657_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_657_, 0, v_p_647_);
lean_closure_set(v___f_657_, 1, v_toBind_650_);
lean_closure_set(v___f_657_, 2, v___f_655_);
lean_closure_set(v___f_657_, 3, v___f_656_);
v___x_658_ = lean_box(v___x_653_);
v___x_659_ = lean_apply_6(v_inst_646_, v___f_652_, lean_box(0), lean_box(0), v_it_648_, v___x_658_, v___f_657_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_allM(lean_object* v_00_u03b1_660_, lean_object* v_00_u03b2_661_, lean_object* v_m_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_p_666_, lean_object* v_it_667_){
_start:
{
lean_object* v_toApplicative_668_; lean_object* v_toBind_669_; lean_object* v_toPure_670_; lean_object* v___f_671_; uint8_t v___x_672_; lean_object* v___x_673_; lean_object* v___f_674_; lean_object* v___f_675_; lean_object* v___f_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v_toApplicative_668_ = lean_ctor_get(v_inst_663_, 0);
lean_inc_ref(v_toApplicative_668_);
v_toBind_669_ = lean_ctor_get(v_inst_663_, 1);
lean_inc(v_toBind_669_);
lean_dec_ref(v_inst_663_);
v_toPure_670_ = lean_ctor_get(v_toApplicative_668_, 1);
lean_inc_n(v_toPure_670_, 2);
lean_dec_ref(v_toApplicative_668_);
v___f_671_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_672_ = 1;
v___x_673_ = lean_box(v___x_672_);
v___f_674_ = lean_alloc_closure((void*)(l_Std_Iter_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_674_, 0, v_toPure_670_);
lean_closure_set(v___f_674_, 1, v___x_673_);
v___f_675_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_675_, 0, v_toPure_670_);
v___f_676_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_676_, 0, v_p_666_);
lean_closure_set(v___f_676_, 1, v_toBind_669_);
lean_closure_set(v___f_676_, 2, v___f_674_);
lean_closure_set(v___f_676_, 3, v___f_675_);
v___x_677_ = lean_box(v___x_672_);
v___x_678_ = lean_apply_6(v_inst_665_, v___f_671_, lean_box(0), lean_box(0), v_it_667_, v___x_677_, v___f_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_allM___boxed(lean_object* v_00_u03b1_679_, lean_object* v_00_u03b2_680_, lean_object* v_m_681_, lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_inst_684_, lean_object* v_p_685_, lean_object* v_it_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Std_Iter_allM(v_00_u03b1_679_, v_00_u03b2_680_, v_m_681_, v_inst_682_, v_inst_683_, v_inst_684_, v_p_685_, v_it_686_);
lean_dec(v_inst_683_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_allM___redArg(lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_p_690_, lean_object* v_it_691_){
_start:
{
lean_object* v_toApplicative_692_; lean_object* v_toBind_693_; lean_object* v_toPure_694_; lean_object* v___f_695_; uint8_t v___x_696_; lean_object* v___x_697_; lean_object* v___f_698_; lean_object* v___f_699_; lean_object* v___f_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_toApplicative_692_ = lean_ctor_get(v_inst_688_, 0);
lean_inc_ref(v_toApplicative_692_);
v_toBind_693_ = lean_ctor_get(v_inst_688_, 1);
lean_inc(v_toBind_693_);
lean_dec_ref(v_inst_688_);
v_toPure_694_ = lean_ctor_get(v_toApplicative_692_, 1);
lean_inc_n(v_toPure_694_, 2);
lean_dec_ref(v_toApplicative_692_);
v___f_695_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_696_ = 1;
v___x_697_ = lean_box(v___x_696_);
v___f_698_ = lean_alloc_closure((void*)(l_Std_Iter_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_698_, 0, v_toPure_694_);
lean_closure_set(v___f_698_, 1, v___x_697_);
v___f_699_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_699_, 0, v_toPure_694_);
v___f_700_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_700_, 0, v_p_690_);
lean_closure_set(v___f_700_, 1, v_toBind_693_);
lean_closure_set(v___f_700_, 2, v___f_698_);
lean_closure_set(v___f_700_, 3, v___f_699_);
v___x_701_ = lean_box(v___x_696_);
v___x_702_ = lean_apply_6(v_inst_689_, v___f_695_, lean_box(0), lean_box(0), v_it_691_, v___x_701_, v___f_700_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_allM(lean_object* v_00_u03b1_703_, lean_object* v_00_u03b2_704_, lean_object* v_m_705_, lean_object* v_inst_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v_p_710_, lean_object* v_it_711_){
_start:
{
lean_object* v_toApplicative_712_; lean_object* v_toBind_713_; lean_object* v_toPure_714_; lean_object* v___f_715_; uint8_t v___x_716_; lean_object* v___x_717_; lean_object* v___f_718_; lean_object* v___f_719_; lean_object* v___f_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_toApplicative_712_ = lean_ctor_get(v_inst_706_, 0);
lean_inc_ref(v_toApplicative_712_);
v_toBind_713_ = lean_ctor_get(v_inst_706_, 1);
lean_inc(v_toBind_713_);
lean_dec_ref(v_inst_706_);
v_toPure_714_ = lean_ctor_get(v_toApplicative_712_, 1);
lean_inc_n(v_toPure_714_, 2);
lean_dec_ref(v_toApplicative_712_);
v___f_715_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_716_ = 1;
v___x_717_ = lean_box(v___x_716_);
v___f_718_ = lean_alloc_closure((void*)(l_Std_Iter_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_718_, 0, v_toPure_714_);
lean_closure_set(v___f_718_, 1, v___x_717_);
v___f_719_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_719_, 0, v_toPure_714_);
v___f_720_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_720_, 0, v_p_710_);
lean_closure_set(v___f_720_, 1, v_toBind_713_);
lean_closure_set(v___f_720_, 2, v___f_718_);
lean_closure_set(v___f_720_, 3, v___f_719_);
v___x_721_ = lean_box(v___x_716_);
v___x_722_ = lean_apply_6(v_inst_708_, v___f_715_, lean_box(0), lean_box(0), v_it_711_, v___x_721_, v___f_720_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_allM___boxed(lean_object* v_00_u03b1_723_, lean_object* v_00_u03b2_724_, lean_object* v_m_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_p_730_, lean_object* v_it_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Std_Iter_Total_allM(v_00_u03b1_723_, v_00_u03b2_724_, v_m_725_, v_inst_726_, v_inst_727_, v_inst_728_, v_inst_729_, v_p_730_, v_it_731_);
lean_dec(v_inst_727_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_all___redArg___lam__1(lean_object* v_p_733_, uint8_t v___x_734_, lean_object* v_x1_735_, lean_object* v_x2_736_, uint8_t v_x3_737_){
_start:
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = lean_apply_1(v_p_733_, v_x1_735_);
v___x_739_ = lean_unbox(v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_738_);
return v___x_740_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_box(v___x_734_);
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_all___redArg___lam__1___boxed(lean_object* v_p_743_, lean_object* v___x_744_, lean_object* v_x1_745_, lean_object* v_x2_746_, lean_object* v_x3_747_){
_start:
{
uint8_t v___x_280__boxed_748_; uint8_t v_x3_283__boxed_749_; lean_object* v_res_750_; 
v___x_280__boxed_748_ = lean_unbox(v___x_744_);
v_x3_283__boxed_749_ = lean_unbox(v_x3_747_);
v_res_750_ = l_Std_Iter_all___redArg___lam__1(v_p_743_, v___x_280__boxed_748_, v_x1_745_, v_x2_746_, v_x3_283__boxed_749_);
return v_res_750_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_all___redArg(lean_object* v_inst_751_, lean_object* v_p_752_, lean_object* v_it_753_){
_start:
{
lean_object* v___f_754_; uint8_t v___x_755_; lean_object* v___x_756_; lean_object* v___f_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___f_754_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_755_ = 1;
v___x_756_ = lean_box(v___x_755_);
v___f_757_ = lean_alloc_closure((void*)(l_Std_Iter_all___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_757_, 0, v_p_752_);
lean_closure_set(v___f_757_, 1, v___x_756_);
v___x_758_ = lean_box(v___x_755_);
v___x_759_ = lean_apply_6(v_inst_751_, v___f_754_, lean_box(0), lean_box(0), v_it_753_, v___x_758_, v___f_757_);
v___x_760_ = lean_unbox(v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_all___redArg___boxed(lean_object* v_inst_761_, lean_object* v_p_762_, lean_object* v_it_763_){
_start:
{
uint8_t v_res_764_; lean_object* v_r_765_; 
v_res_764_ = l_Std_Iter_all___redArg(v_inst_761_, v_p_762_, v_it_763_);
v_r_765_ = lean_box(v_res_764_);
return v_r_765_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_all(lean_object* v_00_u03b1_766_, lean_object* v_00_u03b2_767_, lean_object* v_inst_768_, lean_object* v_inst_769_, lean_object* v_p_770_, lean_object* v_it_771_){
_start:
{
lean_object* v___f_772_; uint8_t v___x_773_; lean_object* v___x_774_; lean_object* v___f_775_; lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v___f_772_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_773_ = 1;
v___x_774_ = lean_box(v___x_773_);
v___f_775_ = lean_alloc_closure((void*)(l_Std_Iter_all___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_775_, 0, v_p_770_);
lean_closure_set(v___f_775_, 1, v___x_774_);
v___x_776_ = lean_box(v___x_773_);
v___x_777_ = lean_apply_6(v_inst_769_, v___f_772_, lean_box(0), lean_box(0), v_it_771_, v___x_776_, v___f_775_);
v___x_778_ = lean_unbox(v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_all___boxed(lean_object* v_00_u03b1_779_, lean_object* v_00_u03b2_780_, lean_object* v_inst_781_, lean_object* v_inst_782_, lean_object* v_p_783_, lean_object* v_it_784_){
_start:
{
uint8_t v_res_785_; lean_object* v_r_786_; 
v_res_785_ = l_Std_Iter_all(v_00_u03b1_779_, v_00_u03b2_780_, v_inst_781_, v_inst_782_, v_p_783_, v_it_784_);
lean_dec(v_inst_781_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_Total_all___redArg(lean_object* v_inst_787_, lean_object* v_p_788_, lean_object* v_it_789_){
_start:
{
lean_object* v___f_790_; uint8_t v___x_791_; lean_object* v___x_792_; lean_object* v___f_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v___f_790_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_791_ = 1;
v___x_792_ = lean_box(v___x_791_);
v___f_793_ = lean_alloc_closure((void*)(l_Std_Iter_all___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_793_, 0, v_p_788_);
lean_closure_set(v___f_793_, 1, v___x_792_);
v___x_794_ = lean_box(v___x_791_);
v___x_795_ = lean_apply_6(v_inst_787_, v___f_790_, lean_box(0), lean_box(0), v_it_789_, v___x_794_, v___f_793_);
v___x_796_ = lean_unbox(v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_all___redArg___boxed(lean_object* v_inst_797_, lean_object* v_p_798_, lean_object* v_it_799_){
_start:
{
uint8_t v_res_800_; lean_object* v_r_801_; 
v_res_800_ = l_Std_Iter_Total_all___redArg(v_inst_797_, v_p_798_, v_it_799_);
v_r_801_ = lean_box(v_res_800_);
return v_r_801_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_Total_all(lean_object* v_00_u03b1_802_, lean_object* v_00_u03b2_803_, lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_p_807_, lean_object* v_it_808_){
_start:
{
lean_object* v___f_809_; uint8_t v___x_810_; lean_object* v___x_811_; lean_object* v___f_812_; lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v___f_809_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_810_ = 1;
v___x_811_ = lean_box(v___x_810_);
v___f_812_ = lean_alloc_closure((void*)(l_Std_Iter_all___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_812_, 0, v_p_807_);
lean_closure_set(v___f_812_, 1, v___x_811_);
v___x_813_ = lean_box(v___x_810_);
v___x_814_ = lean_apply_6(v_inst_805_, v___f_809_, lean_box(0), lean_box(0), v_it_808_, v___x_813_, v___f_812_);
v___x_815_ = lean_unbox(v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_all___boxed(lean_object* v_00_u03b1_816_, lean_object* v_00_u03b2_817_, lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_inst_820_, lean_object* v_p_821_, lean_object* v_it_822_){
_start:
{
uint8_t v_res_823_; lean_object* v_r_824_; 
v_res_823_ = l_Std_Iter_Total_all(v_00_u03b1_816_, v_00_u03b2_817_, v_inst_818_, v_inst_819_, v_inst_820_, v_p_821_, v_it_822_);
lean_dec(v_inst_818_);
v_r_824_ = lean_box(v_res_823_);
return v_r_824_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__1(lean_object* v_toPure_825_, lean_object* v_____do__lift_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = lean_apply_2(v_toPure_825_, lean_box(0), v_____do__lift_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__0(lean_object* v___x_828_, lean_object* v_toPure_829_, lean_object* v_____do__lift_830_){
_start:
{
if (lean_obj_tag(v_____do__lift_830_) == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_828_);
v___x_832_ = lean_apply_2(v_toPure_829_, lean_box(0), v___x_831_);
return v___x_832_;
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec(v___x_828_);
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v_____do__lift_830_);
v___x_834_ = lean_apply_2(v_toPure_829_, lean_box(0), v___x_833_);
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__2(lean_object* v_f_835_, lean_object* v_toBind_836_, lean_object* v___f_837_, lean_object* v___f_838_, lean_object* v_x1_839_, lean_object* v_x2_840_, lean_object* v_x3_841_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = lean_apply_1(v_f_835_, v_x1_839_);
lean_inc(v_toBind_836_);
v___x_843_ = lean_apply_4(v_toBind_836_, lean_box(0), lean_box(0), v___x_842_, v___f_837_);
v___x_844_ = lean_apply_4(v_toBind_836_, lean_box(0), lean_box(0), v___x_843_, v___f_838_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed(lean_object* v_f_845_, lean_object* v_toBind_846_, lean_object* v___f_847_, lean_object* v___f_848_, lean_object* v_x1_849_, lean_object* v_x2_850_, lean_object* v_x3_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_Iter_findSomeM_x3f___redArg___lam__2(v_f_845_, v_toBind_846_, v___f_847_, v___f_848_, v_x1_849_, v_x2_850_, v_x3_851_);
lean_dec(v_x3_851_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg(lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_it_855_, lean_object* v_f_856_){
_start:
{
lean_object* v_toApplicative_857_; lean_object* v_toBind_858_; lean_object* v_toPure_859_; lean_object* v___f_860_; lean_object* v___x_861_; lean_object* v___f_862_; lean_object* v___f_863_; lean_object* v___f_864_; lean_object* v___x_865_; 
v_toApplicative_857_ = lean_ctor_get(v_inst_853_, 0);
lean_inc_ref(v_toApplicative_857_);
v_toBind_858_ = lean_ctor_get(v_inst_853_, 1);
lean_inc(v_toBind_858_);
lean_dec_ref(v_inst_853_);
v_toPure_859_ = lean_ctor_get(v_toApplicative_857_, 1);
lean_inc_n(v_toPure_859_, 2);
lean_dec_ref(v_toApplicative_857_);
v___f_860_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_861_ = lean_box(0);
v___f_862_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_862_, 0, v_toPure_859_);
v___f_863_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_863_, 0, v___x_861_);
lean_closure_set(v___f_863_, 1, v_toPure_859_);
v___f_864_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_864_, 0, v_f_856_);
lean_closure_set(v___f_864_, 1, v_toBind_858_);
lean_closure_set(v___f_864_, 2, v___f_863_);
lean_closure_set(v___f_864_, 3, v___f_862_);
v___x_865_ = lean_apply_6(v_inst_854_, v___f_860_, lean_box(0), lean_box(0), v_it_855_, v___x_861_, v___f_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f(lean_object* v_00_u03b1_866_, lean_object* v_00_u03b2_867_, lean_object* v_00_u03b3_868_, lean_object* v_m_869_, lean_object* v_inst_870_, lean_object* v_inst_871_, lean_object* v_inst_872_, lean_object* v_it_873_, lean_object* v_f_874_){
_start:
{
lean_object* v_toApplicative_875_; lean_object* v_toBind_876_; lean_object* v_toPure_877_; lean_object* v___f_878_; lean_object* v___x_879_; lean_object* v___f_880_; lean_object* v___f_881_; lean_object* v___f_882_; lean_object* v___x_883_; 
v_toApplicative_875_ = lean_ctor_get(v_inst_870_, 0);
lean_inc_ref(v_toApplicative_875_);
v_toBind_876_ = lean_ctor_get(v_inst_870_, 1);
lean_inc(v_toBind_876_);
lean_dec_ref(v_inst_870_);
v_toPure_877_ = lean_ctor_get(v_toApplicative_875_, 1);
lean_inc_n(v_toPure_877_, 2);
lean_dec_ref(v_toApplicative_875_);
v___f_878_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_879_ = lean_box(0);
v___f_880_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_880_, 0, v_toPure_877_);
v___f_881_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_881_, 0, v___x_879_);
lean_closure_set(v___f_881_, 1, v_toPure_877_);
v___f_882_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_882_, 0, v_f_874_);
lean_closure_set(v___f_882_, 1, v_toBind_876_);
lean_closure_set(v___f_882_, 2, v___f_881_);
lean_closure_set(v___f_882_, 3, v___f_880_);
v___x_883_ = lean_apply_6(v_inst_872_, v___f_878_, lean_box(0), lean_box(0), v_it_873_, v___x_879_, v___f_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___boxed(lean_object* v_00_u03b1_884_, lean_object* v_00_u03b2_885_, lean_object* v_00_u03b3_886_, lean_object* v_m_887_, lean_object* v_inst_888_, lean_object* v_inst_889_, lean_object* v_inst_890_, lean_object* v_it_891_, lean_object* v_f_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Std_Iter_findSomeM_x3f(v_00_u03b1_884_, v_00_u03b2_885_, v_00_u03b3_886_, v_m_887_, v_inst_888_, v_inst_889_, v_inst_890_, v_it_891_, v_f_892_);
lean_dec(v_inst_889_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f___redArg(lean_object* v_inst_894_, lean_object* v_inst_895_, lean_object* v_it_896_, lean_object* v_f_897_){
_start:
{
lean_object* v_toApplicative_898_; lean_object* v_toBind_899_; lean_object* v_toPure_900_; lean_object* v___f_901_; lean_object* v___x_902_; lean_object* v___f_903_; lean_object* v___f_904_; lean_object* v___f_905_; lean_object* v___x_906_; 
v_toApplicative_898_ = lean_ctor_get(v_inst_894_, 0);
lean_inc_ref(v_toApplicative_898_);
v_toBind_899_ = lean_ctor_get(v_inst_894_, 1);
lean_inc(v_toBind_899_);
lean_dec_ref(v_inst_894_);
v_toPure_900_ = lean_ctor_get(v_toApplicative_898_, 1);
lean_inc_n(v_toPure_900_, 2);
lean_dec_ref(v_toApplicative_898_);
v___f_901_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_902_ = lean_box(0);
v___f_903_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_903_, 0, v___x_902_);
lean_closure_set(v___f_903_, 1, v_toPure_900_);
v___f_904_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_904_, 0, v_toPure_900_);
v___f_905_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_905_, 0, v_f_897_);
lean_closure_set(v___f_905_, 1, v_toBind_899_);
lean_closure_set(v___f_905_, 2, v___f_903_);
lean_closure_set(v___f_905_, 3, v___f_904_);
v___x_906_ = lean_apply_6(v_inst_895_, v___f_901_, lean_box(0), lean_box(0), v_it_896_, v___x_902_, v___f_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f(lean_object* v_00_u03b1_907_, lean_object* v_00_u03b2_908_, lean_object* v_00_u03b3_909_, lean_object* v_m_910_, lean_object* v_inst_911_, lean_object* v_inst_912_, lean_object* v_inst_913_, lean_object* v_inst_914_, lean_object* v_it_915_, lean_object* v_f_916_){
_start:
{
lean_object* v_toApplicative_917_; lean_object* v_toBind_918_; lean_object* v_toPure_919_; lean_object* v___f_920_; lean_object* v___x_921_; lean_object* v___f_922_; lean_object* v___f_923_; lean_object* v___f_924_; lean_object* v___x_925_; 
v_toApplicative_917_ = lean_ctor_get(v_inst_911_, 0);
lean_inc_ref(v_toApplicative_917_);
v_toBind_918_ = lean_ctor_get(v_inst_911_, 1);
lean_inc(v_toBind_918_);
lean_dec_ref(v_inst_911_);
v_toPure_919_ = lean_ctor_get(v_toApplicative_917_, 1);
lean_inc_n(v_toPure_919_, 2);
lean_dec_ref(v_toApplicative_917_);
v___f_920_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_921_ = lean_box(0);
v___f_922_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_922_, 0, v___x_921_);
lean_closure_set(v___f_922_, 1, v_toPure_919_);
v___f_923_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_923_, 0, v_toPure_919_);
v___f_924_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_924_, 0, v_f_916_);
lean_closure_set(v___f_924_, 1, v_toBind_918_);
lean_closure_set(v___f_924_, 2, v___f_922_);
lean_closure_set(v___f_924_, 3, v___f_923_);
v___x_925_ = lean_apply_6(v_inst_913_, v___f_920_, lean_box(0), lean_box(0), v_it_915_, v___x_921_, v___f_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f___boxed(lean_object* v_00_u03b1_926_, lean_object* v_00_u03b2_927_, lean_object* v_00_u03b3_928_, lean_object* v_m_929_, lean_object* v_inst_930_, lean_object* v_inst_931_, lean_object* v_inst_932_, lean_object* v_inst_933_, lean_object* v_it_934_, lean_object* v_f_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Std_Iter_Total_findSomeM_x3f(v_00_u03b1_926_, v_00_u03b2_927_, v_00_u03b3_928_, v_m_929_, v_inst_930_, v_inst_931_, v_inst_932_, v_inst_933_, v_it_934_, v_f_935_);
lean_dec(v_inst_931_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg___lam__1(lean_object* v_f_937_, lean_object* v___x_938_, lean_object* v_x1_939_, lean_object* v_x2_940_, lean_object* v_x3_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = lean_apply_1(v_f_937_, v_x1_939_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v___x_943_; 
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_938_);
return v___x_943_;
}
else
{
lean_object* v___x_944_; 
lean_dec(v___x_938_);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg___lam__1___boxed(lean_object* v_f_945_, lean_object* v___x_946_, lean_object* v_x1_947_, lean_object* v_x2_948_, lean_object* v_x3_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Std_Iter_findSome_x3f___redArg___lam__1(v_f_945_, v___x_946_, v_x1_947_, v_x2_948_, v_x3_949_);
lean_dec(v_x3_949_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg(lean_object* v_inst_951_, lean_object* v_it_952_, lean_object* v_f_953_){
_start:
{
lean_object* v___f_954_; lean_object* v___x_955_; lean_object* v___f_956_; lean_object* v___x_957_; 
v___f_954_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_955_ = lean_box(0);
v___f_956_ = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_956_, 0, v_f_953_);
lean_closure_set(v___f_956_, 1, v___x_955_);
v___x_957_ = lean_apply_6(v_inst_951_, v___f_954_, lean_box(0), lean_box(0), v_it_952_, v___x_955_, v___f_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f(lean_object* v_00_u03b1_958_, lean_object* v_00_u03b2_959_, lean_object* v_00_u03b3_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_it_963_, lean_object* v_f_964_){
_start:
{
lean_object* v___f_965_; lean_object* v___x_966_; lean_object* v___f_967_; lean_object* v___x_968_; 
v___f_965_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_966_ = lean_box(0);
v___f_967_ = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_967_, 0, v_f_964_);
lean_closure_set(v___f_967_, 1, v___x_966_);
v___x_968_ = lean_apply_6(v_inst_962_, v___f_965_, lean_box(0), lean_box(0), v_it_963_, v___x_966_, v___f_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___boxed(lean_object* v_00_u03b1_969_, lean_object* v_00_u03b2_970_, lean_object* v_00_u03b3_971_, lean_object* v_inst_972_, lean_object* v_inst_973_, lean_object* v_it_974_, lean_object* v_f_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Std_Iter_findSome_x3f(v_00_u03b1_969_, v_00_u03b2_970_, v_00_u03b3_971_, v_inst_972_, v_inst_973_, v_it_974_, v_f_975_);
lean_dec(v_inst_972_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSome_x3f___redArg(lean_object* v_inst_977_, lean_object* v_it_978_, lean_object* v_f_979_){
_start:
{
lean_object* v___f_980_; lean_object* v___x_981_; lean_object* v___f_982_; lean_object* v___x_983_; 
v___f_980_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_981_ = lean_box(0);
v___f_982_ = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_982_, 0, v_f_979_);
lean_closure_set(v___f_982_, 1, v___x_981_);
v___x_983_ = lean_apply_6(v_inst_977_, v___f_980_, lean_box(0), lean_box(0), v_it_978_, v___x_981_, v___f_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSome_x3f(lean_object* v_00_u03b1_984_, lean_object* v_00_u03b2_985_, lean_object* v_00_u03b3_986_, lean_object* v_inst_987_, lean_object* v_inst_988_, lean_object* v_inst_989_, lean_object* v_it_990_, lean_object* v_f_991_){
_start:
{
lean_object* v___f_992_; lean_object* v___x_993_; lean_object* v___f_994_; lean_object* v___x_995_; 
v___f_992_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_993_ = lean_box(0);
v___f_994_ = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_994_, 0, v_f_991_);
lean_closure_set(v___f_994_, 1, v___x_993_);
v___x_995_ = lean_apply_6(v_inst_988_, v___f_992_, lean_box(0), lean_box(0), v_it_990_, v___x_993_, v___f_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSome_x3f___boxed(lean_object* v_00_u03b1_996_, lean_object* v_00_u03b2_997_, lean_object* v_00_u03b3_998_, lean_object* v_inst_999_, lean_object* v_inst_1000_, lean_object* v_inst_1001_, lean_object* v_it_1002_, lean_object* v_f_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Std_Iter_Total_findSome_x3f(v_00_u03b1_996_, v_00_u03b2_997_, v_00_u03b3_998_, v_inst_999_, v_inst_1000_, v_inst_1001_, v_it_1002_, v_f_1003_);
lean_dec(v_inst_999_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__3(lean_object* v_toPure_1005_, lean_object* v___x_1006_, lean_object* v_x1_1007_, uint8_t v_____do__lift_1008_){
_start:
{
if (v_____do__lift_1008_ == 0)
{
lean_object* v___x_1009_; 
lean_dec(v_x1_1007_);
v___x_1009_ = lean_apply_2(v_toPure_1005_, lean_box(0), v___x_1006_);
return v___x_1009_;
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec(v___x_1006_);
v___x_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1010_, 0, v_x1_1007_);
v___x_1011_ = lean_apply_2(v_toPure_1005_, lean_box(0), v___x_1010_);
return v___x_1011_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__3___boxed(lean_object* v_toPure_1012_, lean_object* v___x_1013_, lean_object* v_x1_1014_, lean_object* v_____do__lift_1015_){
_start:
{
uint8_t v_____do__lift_191__boxed_1016_; lean_object* v_res_1017_; 
v_____do__lift_191__boxed_1016_ = lean_unbox(v_____do__lift_1015_);
v_res_1017_ = l_Std_Iter_findM_x3f___redArg___lam__3(v_toPure_1012_, v___x_1013_, v_x1_1014_, v_____do__lift_191__boxed_1016_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__0(lean_object* v_toPure_1018_, lean_object* v___x_1019_, lean_object* v_f_1020_, lean_object* v_toBind_1021_, lean_object* v___f_1022_, lean_object* v___f_1023_, lean_object* v_x1_1024_, lean_object* v_x2_1025_, lean_object* v_x3_1026_){
_start:
{
lean_object* v___f_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
lean_inc(v_x1_1024_);
v___f_1027_ = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_1027_, 0, v_toPure_1018_);
lean_closure_set(v___f_1027_, 1, v___x_1019_);
lean_closure_set(v___f_1027_, 2, v_x1_1024_);
v___x_1028_ = lean_apply_1(v_f_1020_, v_x1_1024_);
lean_inc_n(v_toBind_1021_, 2);
v___x_1029_ = lean_apply_4(v_toBind_1021_, lean_box(0), lean_box(0), v___x_1028_, v___f_1027_);
v___x_1030_ = lean_apply_4(v_toBind_1021_, lean_box(0), lean_box(0), v___x_1029_, v___f_1022_);
v___x_1031_ = lean_apply_4(v_toBind_1021_, lean_box(0), lean_box(0), v___x_1030_, v___f_1023_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_1032_, lean_object* v___x_1033_, lean_object* v_f_1034_, lean_object* v_toBind_1035_, lean_object* v___f_1036_, lean_object* v___f_1037_, lean_object* v_x1_1038_, lean_object* v_x2_1039_, lean_object* v_x3_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Std_Iter_findM_x3f___redArg___lam__0(v_toPure_1032_, v___x_1033_, v_f_1034_, v_toBind_1035_, v___f_1036_, v___f_1037_, v_x1_1038_, v_x2_1039_, v_x3_1040_);
lean_dec(v_x3_1040_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg(lean_object* v_inst_1042_, lean_object* v_inst_1043_, lean_object* v_it_1044_, lean_object* v_f_1045_){
_start:
{
lean_object* v_toApplicative_1046_; lean_object* v_toBind_1047_; lean_object* v_toPure_1048_; lean_object* v___f_1049_; lean_object* v___f_1050_; lean_object* v___x_1051_; lean_object* v___f_1052_; lean_object* v___f_1053_; lean_object* v___x_1054_; 
v_toApplicative_1046_ = lean_ctor_get(v_inst_1042_, 0);
lean_inc_ref(v_toApplicative_1046_);
v_toBind_1047_ = lean_ctor_get(v_inst_1042_, 1);
lean_inc(v_toBind_1047_);
lean_dec_ref(v_inst_1042_);
v_toPure_1048_ = lean_ctor_get(v_toApplicative_1046_, 1);
lean_inc_n(v_toPure_1048_, 3);
lean_dec_ref(v_toApplicative_1046_);
v___f_1049_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_1050_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1050_, 0, v_toPure_1048_);
v___x_1051_ = lean_box(0);
v___f_1052_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1052_, 0, v___x_1051_);
lean_closure_set(v___f_1052_, 1, v_toPure_1048_);
v___f_1053_ = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1053_, 0, v_toPure_1048_);
lean_closure_set(v___f_1053_, 1, v___x_1051_);
lean_closure_set(v___f_1053_, 2, v_f_1045_);
lean_closure_set(v___f_1053_, 3, v_toBind_1047_);
lean_closure_set(v___f_1053_, 4, v___f_1052_);
lean_closure_set(v___f_1053_, 5, v___f_1050_);
v___x_1054_ = lean_apply_6(v_inst_1043_, v___f_1049_, lean_box(0), lean_box(0), v_it_1044_, v___x_1051_, v___f_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f(lean_object* v_00_u03b1_1055_, lean_object* v_00_u03b2_1056_, lean_object* v_m_1057_, lean_object* v_inst_1058_, lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_it_1061_, lean_object* v_f_1062_){
_start:
{
lean_object* v_toApplicative_1063_; lean_object* v_toBind_1064_; lean_object* v_toPure_1065_; lean_object* v___f_1066_; lean_object* v___f_1067_; lean_object* v___x_1068_; lean_object* v___f_1069_; lean_object* v___f_1070_; lean_object* v___x_1071_; 
v_toApplicative_1063_ = lean_ctor_get(v_inst_1058_, 0);
lean_inc_ref(v_toApplicative_1063_);
v_toBind_1064_ = lean_ctor_get(v_inst_1058_, 1);
lean_inc(v_toBind_1064_);
lean_dec_ref(v_inst_1058_);
v_toPure_1065_ = lean_ctor_get(v_toApplicative_1063_, 1);
lean_inc_n(v_toPure_1065_, 3);
lean_dec_ref(v_toApplicative_1063_);
v___f_1066_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_1067_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1067_, 0, v_toPure_1065_);
v___x_1068_ = lean_box(0);
v___f_1069_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1069_, 0, v___x_1068_);
lean_closure_set(v___f_1069_, 1, v_toPure_1065_);
v___f_1070_ = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1070_, 0, v_toPure_1065_);
lean_closure_set(v___f_1070_, 1, v___x_1068_);
lean_closure_set(v___f_1070_, 2, v_f_1062_);
lean_closure_set(v___f_1070_, 3, v_toBind_1064_);
lean_closure_set(v___f_1070_, 4, v___f_1069_);
lean_closure_set(v___f_1070_, 5, v___f_1067_);
v___x_1071_ = lean_apply_6(v_inst_1060_, v___f_1066_, lean_box(0), lean_box(0), v_it_1061_, v___x_1068_, v___f_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___boxed(lean_object* v_00_u03b1_1072_, lean_object* v_00_u03b2_1073_, lean_object* v_m_1074_, lean_object* v_inst_1075_, lean_object* v_inst_1076_, lean_object* v_inst_1077_, lean_object* v_it_1078_, lean_object* v_f_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Std_Iter_findM_x3f(v_00_u03b1_1072_, v_00_u03b2_1073_, v_m_1074_, v_inst_1075_, v_inst_1076_, v_inst_1077_, v_it_1078_, v_f_1079_);
lean_dec(v_inst_1076_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f___redArg(lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_it_1083_, lean_object* v_f_1084_){
_start:
{
lean_object* v_toApplicative_1085_; lean_object* v_toBind_1086_; lean_object* v_toPure_1087_; lean_object* v___f_1088_; lean_object* v___f_1089_; lean_object* v___x_1090_; lean_object* v___f_1091_; lean_object* v___f_1092_; lean_object* v___x_1093_; 
v_toApplicative_1085_ = lean_ctor_get(v_inst_1081_, 0);
lean_inc_ref(v_toApplicative_1085_);
v_toBind_1086_ = lean_ctor_get(v_inst_1081_, 1);
lean_inc(v_toBind_1086_);
lean_dec_ref(v_inst_1081_);
v_toPure_1087_ = lean_ctor_get(v_toApplicative_1085_, 1);
lean_inc_n(v_toPure_1087_, 3);
lean_dec_ref(v_toApplicative_1085_);
v___f_1088_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_1089_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1089_, 0, v_toPure_1087_);
v___x_1090_ = lean_box(0);
v___f_1091_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1091_, 0, v___x_1090_);
lean_closure_set(v___f_1091_, 1, v_toPure_1087_);
v___f_1092_ = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1092_, 0, v_toPure_1087_);
lean_closure_set(v___f_1092_, 1, v___x_1090_);
lean_closure_set(v___f_1092_, 2, v_f_1084_);
lean_closure_set(v___f_1092_, 3, v_toBind_1086_);
lean_closure_set(v___f_1092_, 4, v___f_1091_);
lean_closure_set(v___f_1092_, 5, v___f_1089_);
v___x_1093_ = lean_apply_6(v_inst_1082_, v___f_1088_, lean_box(0), lean_box(0), v_it_1083_, v___x_1090_, v___f_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f(lean_object* v_00_u03b1_1094_, lean_object* v_00_u03b2_1095_, lean_object* v_m_1096_, lean_object* v_inst_1097_, lean_object* v_inst_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_it_1101_, lean_object* v_f_1102_){
_start:
{
lean_object* v_toApplicative_1103_; lean_object* v_toBind_1104_; lean_object* v_toPure_1105_; lean_object* v___f_1106_; lean_object* v___f_1107_; lean_object* v___x_1108_; lean_object* v___f_1109_; lean_object* v___f_1110_; lean_object* v___x_1111_; 
v_toApplicative_1103_ = lean_ctor_get(v_inst_1097_, 0);
lean_inc_ref(v_toApplicative_1103_);
v_toBind_1104_ = lean_ctor_get(v_inst_1097_, 1);
lean_inc(v_toBind_1104_);
lean_dec_ref(v_inst_1097_);
v_toPure_1105_ = lean_ctor_get(v_toApplicative_1103_, 1);
lean_inc_n(v_toPure_1105_, 3);
lean_dec_ref(v_toApplicative_1103_);
v___f_1106_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_1107_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1107_, 0, v_toPure_1105_);
v___x_1108_ = lean_box(0);
v___f_1109_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1109_, 0, v___x_1108_);
lean_closure_set(v___f_1109_, 1, v_toPure_1105_);
v___f_1110_ = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1110_, 0, v_toPure_1105_);
lean_closure_set(v___f_1110_, 1, v___x_1108_);
lean_closure_set(v___f_1110_, 2, v_f_1102_);
lean_closure_set(v___f_1110_, 3, v_toBind_1104_);
lean_closure_set(v___f_1110_, 4, v___f_1109_);
lean_closure_set(v___f_1110_, 5, v___f_1107_);
v___x_1111_ = lean_apply_6(v_inst_1099_, v___f_1106_, lean_box(0), lean_box(0), v_it_1101_, v___x_1108_, v___f_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f___boxed(lean_object* v_00_u03b1_1112_, lean_object* v_00_u03b2_1113_, lean_object* v_m_1114_, lean_object* v_inst_1115_, lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_it_1119_, lean_object* v_f_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Std_Iter_Total_findM_x3f(v_00_u03b1_1112_, v_00_u03b2_1113_, v_m_1114_, v_inst_1115_, v_inst_1116_, v_inst_1117_, v_inst_1118_, v_it_1119_, v_f_1120_);
lean_dec(v_inst_1116_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg___lam__1(lean_object* v_f_1122_, lean_object* v___x_1123_, lean_object* v_x1_1124_, lean_object* v_x2_1125_, lean_object* v_x3_1126_){
_start:
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
lean_inc(v_x1_1124_);
v___x_1127_ = lean_apply_1(v_f_1122_, v_x1_1124_);
v___x_1128_ = lean_unbox(v___x_1127_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; 
lean_dec(v_x1_1124_);
v___x_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1123_);
return v___x_1129_;
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v___x_1123_);
v___x_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_x1_1124_);
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
return v___x_1131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg___lam__1___boxed(lean_object* v_f_1132_, lean_object* v___x_1133_, lean_object* v_x1_1134_, lean_object* v_x2_1135_, lean_object* v_x3_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Std_Iter_find_x3f___redArg___lam__1(v_f_1132_, v___x_1133_, v_x1_1134_, v_x2_1135_, v_x3_1136_);
lean_dec(v_x3_1136_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg(lean_object* v_inst_1138_, lean_object* v_it_1139_, lean_object* v_f_1140_){
_start:
{
lean_object* v___f_1141_; lean_object* v___x_1142_; lean_object* v___f_1143_; lean_object* v___x_1144_; 
v___f_1141_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1142_ = lean_box(0);
v___f_1143_ = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1143_, 0, v_f_1140_);
lean_closure_set(v___f_1143_, 1, v___x_1142_);
v___x_1144_ = lean_apply_6(v_inst_1138_, v___f_1141_, lean_box(0), lean_box(0), v_it_1139_, v___x_1142_, v___f_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f(lean_object* v_00_u03b1_1145_, lean_object* v_00_u03b2_1146_, lean_object* v_inst_1147_, lean_object* v_inst_1148_, lean_object* v_it_1149_, lean_object* v_f_1150_){
_start:
{
lean_object* v___f_1151_; lean_object* v___x_1152_; lean_object* v___f_1153_; lean_object* v___x_1154_; 
v___f_1151_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1152_ = lean_box(0);
v___f_1153_ = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1153_, 0, v_f_1150_);
lean_closure_set(v___f_1153_, 1, v___x_1152_);
v___x_1154_ = lean_apply_6(v_inst_1148_, v___f_1151_, lean_box(0), lean_box(0), v_it_1149_, v___x_1152_, v___f_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___boxed(lean_object* v_00_u03b1_1155_, lean_object* v_00_u03b2_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_, lean_object* v_it_1159_, lean_object* v_f_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Std_Iter_find_x3f(v_00_u03b1_1155_, v_00_u03b2_1156_, v_inst_1157_, v_inst_1158_, v_it_1159_, v_f_1160_);
lean_dec(v_inst_1157_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_find_x3f___redArg(lean_object* v_inst_1162_, lean_object* v_it_1163_, lean_object* v_f_1164_){
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
LEAN_EXPORT lean_object* l_Std_Iter_Total_find_x3f(lean_object* v_00_u03b1_1169_, lean_object* v_00_u03b2_1170_, lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_inst_1173_, lean_object* v_it_1174_, lean_object* v_f_1175_){
_start:
{
lean_object* v___f_1176_; lean_object* v___x_1177_; lean_object* v___f_1178_; lean_object* v___x_1179_; 
v___f_1176_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1177_ = lean_box(0);
v___f_1178_ = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1178_, 0, v_f_1175_);
lean_closure_set(v___f_1178_, 1, v___x_1177_);
v___x_1179_ = lean_apply_6(v_inst_1172_, v___f_1176_, lean_box(0), lean_box(0), v_it_1174_, v___x_1177_, v___f_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_find_x3f___boxed(lean_object* v_00_u03b1_1180_, lean_object* v_00_u03b2_1181_, lean_object* v_inst_1182_, lean_object* v_inst_1183_, lean_object* v_inst_1184_, lean_object* v_it_1185_, lean_object* v_f_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Std_Iter_Total_find_x3f(v_00_u03b1_1180_, v_00_u03b2_1181_, v_inst_1182_, v_inst_1183_, v_inst_1184_, v_it_1185_, v_f_1186_);
lean_dec(v_inst_1182_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___redArg___lam__0(lean_object* v_x_1188_, lean_object* v_x_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_apply_1(v___y_1190_, v___y_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___redArg___lam__1(lean_object* v_b_1193_, lean_object* v_x_1194_, lean_object* v_x_1195_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1196_, 0, v_b_1193_);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___redArg___lam__1___boxed(lean_object* v_b_1198_, lean_object* v_x_1199_, lean_object* v_x_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Std_Iter_first_x3f___redArg___lam__1(v_b_1198_, v_x_1199_, v_x_1200_);
lean_dec(v_x_1200_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___redArg(lean_object* v_inst_1204_, lean_object* v_it_1205_){
_start:
{
lean_object* v___f_1206_; lean_object* v___f_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___f_1206_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1207_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__1));
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_apply_6(v_inst_1204_, v___f_1206_, lean_box(0), lean_box(0), v_it_1205_, v___x_1208_, v___f_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f(lean_object* v_00_u03b1_1210_, lean_object* v_00_u03b2_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_it_1214_){
_start:
{
lean_object* v___f_1215_; lean_object* v___f_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___f_1215_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1216_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__1));
v___x_1217_ = lean_box(0);
v___x_1218_ = lean_apply_6(v_inst_1213_, v___f_1215_, lean_box(0), lean_box(0), v_it_1214_, v___x_1217_, v___f_1216_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___boxed(lean_object* v_00_u03b1_1219_, lean_object* v_00_u03b2_1220_, lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_it_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Std_Iter_first_x3f(v_00_u03b1_1219_, v_00_u03b2_1220_, v_inst_1221_, v_inst_1222_, v_it_1223_);
lean_dec(v_inst_1221_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_first_x3f___redArg(lean_object* v_inst_1225_, lean_object* v_it_1226_){
_start:
{
lean_object* v___f_1227_; lean_object* v___f_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___f_1227_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1228_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__1));
v___x_1229_ = lean_box(0);
v___x_1230_ = lean_apply_6(v_inst_1225_, v___f_1227_, lean_box(0), lean_box(0), v_it_1226_, v___x_1229_, v___f_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_first_x3f(lean_object* v_00_u03b1_1231_, lean_object* v_00_u03b2_1232_, lean_object* v_inst_1233_, lean_object* v_inst_1234_, lean_object* v_inst_1235_, lean_object* v_it_1236_){
_start:
{
lean_object* v___f_1237_; lean_object* v___f_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___f_1237_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1238_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__1));
v___x_1239_ = lean_box(0);
v___x_1240_ = lean_apply_6(v_inst_1234_, v___f_1237_, lean_box(0), lean_box(0), v_it_1236_, v___x_1239_, v___f_1238_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_first_x3f___boxed(lean_object* v_00_u03b1_1241_, lean_object* v_00_u03b2_1242_, lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_, lean_object* v_it_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Std_Iter_Total_first_x3f(v_00_u03b1_1241_, v_00_u03b2_1242_, v_inst_1243_, v_inst_1244_, v_inst_1245_, v_it_1246_);
lean_dec(v_inst_1243_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_isEmpty___redArg___lam__1(lean_object* v_x_1251_, lean_object* v_x_1252_, uint8_t v_x_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = ((lean_object*)(l_Std_Iter_isEmpty___redArg___lam__1___closed__0));
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_isEmpty___redArg___lam__1___boxed(lean_object* v_x_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_){
_start:
{
uint8_t v_x_151__boxed_1258_; lean_object* v_res_1259_; 
v_x_151__boxed_1258_ = lean_unbox(v_x_1257_);
v_res_1259_ = l_Std_Iter_isEmpty___redArg___lam__1(v_x_1255_, v_x_1256_, v_x_151__boxed_1258_);
lean_dec(v_x_1255_);
return v_res_1259_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_isEmpty___redArg(lean_object* v_inst_1261_, lean_object* v_it_1262_){
_start:
{
lean_object* v___f_1263_; lean_object* v___f_1264_; uint8_t v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___f_1263_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1264_ = ((lean_object*)(l_Std_Iter_isEmpty___redArg___closed__0));
v___x_1265_ = 1;
v___x_1266_ = lean_box(v___x_1265_);
v___x_1267_ = lean_apply_6(v_inst_1261_, v___f_1263_, lean_box(0), lean_box(0), v_it_1262_, v___x_1266_, v___f_1264_);
v___x_1268_ = lean_unbox(v___x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_isEmpty___redArg___boxed(lean_object* v_inst_1269_, lean_object* v_it_1270_){
_start:
{
uint8_t v_res_1271_; lean_object* v_r_1272_; 
v_res_1271_ = l_Std_Iter_isEmpty___redArg(v_inst_1269_, v_it_1270_);
v_r_1272_ = lean_box(v_res_1271_);
return v_r_1272_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_isEmpty(lean_object* v_00_u03b1_1273_, lean_object* v_00_u03b2_1274_, lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_it_1277_){
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
LEAN_EXPORT lean_object* l_Std_Iter_isEmpty___boxed(lean_object* v_00_u03b1_1284_, lean_object* v_00_u03b2_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_it_1288_){
_start:
{
uint8_t v_res_1289_; lean_object* v_r_1290_; 
v_res_1289_ = l_Std_Iter_isEmpty(v_00_u03b1_1284_, v_00_u03b2_1285_, v_inst_1286_, v_inst_1287_, v_it_1288_);
lean_dec(v_inst_1286_);
v_r_1290_ = lean_box(v_res_1289_);
return v_r_1290_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_Total_isEmpty___redArg(lean_object* v_inst_1291_, lean_object* v_it_1292_){
_start:
{
lean_object* v___f_1293_; lean_object* v___f_1294_; uint8_t v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___f_1293_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1294_ = ((lean_object*)(l_Std_Iter_isEmpty___redArg___closed__0));
v___x_1295_ = 1;
v___x_1296_ = lean_box(v___x_1295_);
v___x_1297_ = lean_apply_6(v_inst_1291_, v___f_1293_, lean_box(0), lean_box(0), v_it_1292_, v___x_1296_, v___f_1294_);
v___x_1298_ = lean_unbox(v___x_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_isEmpty___redArg___boxed(lean_object* v_inst_1299_, lean_object* v_it_1300_){
_start:
{
uint8_t v_res_1301_; lean_object* v_r_1302_; 
v_res_1301_ = l_Std_Iter_Total_isEmpty___redArg(v_inst_1299_, v_it_1300_);
v_r_1302_ = lean_box(v_res_1301_);
return v_r_1302_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_Total_isEmpty(lean_object* v_00_u03b1_1303_, lean_object* v_00_u03b2_1304_, lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_it_1308_){
_start:
{
lean_object* v___f_1309_; lean_object* v___f_1310_; uint8_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___f_1309_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1310_ = ((lean_object*)(l_Std_Iter_isEmpty___redArg___closed__0));
v___x_1311_ = 1;
v___x_1312_ = lean_box(v___x_1311_);
v___x_1313_ = lean_apply_6(v_inst_1306_, v___f_1309_, lean_box(0), lean_box(0), v_it_1308_, v___x_1312_, v___f_1310_);
v___x_1314_ = lean_unbox(v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_isEmpty___boxed(lean_object* v_00_u03b1_1315_, lean_object* v_00_u03b2_1316_, lean_object* v_inst_1317_, lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_it_1320_){
_start:
{
uint8_t v_res_1321_; lean_object* v_r_1322_; 
v_res_1321_ = l_Std_Iter_Total_isEmpty(v_00_u03b1_1315_, v_00_u03b2_1316_, v_inst_1317_, v_inst_1318_, v_inst_1319_, v_it_1320_);
lean_dec(v_inst_1317_);
v_r_1322_ = lean_box(v_res_1321_);
return v_r_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_length___redArg___lam__0(lean_object* v_x_1323_, lean_object* v_x_1324_, lean_object* v_f_1325_, lean_object* v_x_1326_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_apply_1(v_f_1325_, v_x_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_length___redArg___lam__1(lean_object* v_x1_1328_, lean_object* v_x2_1329_, lean_object* v_x3_1330_){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = lean_unsigned_to_nat(1u);
v___x_1332_ = lean_nat_add(v_x3_1330_, v___x_1331_);
v___x_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_length___redArg___lam__1___boxed(lean_object* v_x1_1334_, lean_object* v_x2_1335_, lean_object* v_x3_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Std_Iter_length___redArg___lam__1(v_x1_1334_, v_x2_1335_, v_x3_1336_);
lean_dec(v_x3_1336_);
lean_dec(v_x1_1334_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_length___redArg(lean_object* v_inst_1340_, lean_object* v_it_1341_){
_start:
{
lean_object* v___f_1342_; lean_object* v___f_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___f_1342_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__0));
v___f_1343_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__1));
v___x_1344_ = lean_unsigned_to_nat(0u);
v___x_1345_ = lean_apply_6(v_inst_1340_, v___f_1342_, lean_box(0), lean_box(0), v_it_1341_, v___x_1344_, v___f_1343_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_length(lean_object* v_00_u03b1_1346_, lean_object* v_00_u03b2_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_it_1350_){
_start:
{
lean_object* v___f_1351_; lean_object* v___f_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___f_1351_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__0));
v___f_1352_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__1));
v___x_1353_ = lean_unsigned_to_nat(0u);
v___x_1354_ = lean_apply_6(v_inst_1349_, v___f_1351_, lean_box(0), lean_box(0), v_it_1350_, v___x_1353_, v___f_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_length___boxed(lean_object* v_00_u03b1_1355_, lean_object* v_00_u03b2_1356_, lean_object* v_inst_1357_, lean_object* v_inst_1358_, lean_object* v_it_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Std_Iter_length(v_00_u03b1_1355_, v_00_u03b2_1356_, v_inst_1357_, v_inst_1358_, v_it_1359_);
lean_dec(v_inst_1357_);
return v_res_1360_;
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
