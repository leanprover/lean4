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
LEAN_EXPORT lean_object* l_Std_Iter_Partial_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_fold___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSomeM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSomeM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSome_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSome_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Iter_count___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_count(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_count___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_size___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_size(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_count___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_count(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_count___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_size___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_size(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Iter_Partial_foldM___redArg(lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_f_307_, lean_object* v_init_308_, lean_object* v_it_309_){
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
LEAN_EXPORT lean_object* l_Std_Iter_Partial_foldM(lean_object* v_m_319_, lean_object* v_inst_320_, lean_object* v_00_u03b1_321_, lean_object* v_00_u03b2_322_, lean_object* v_00_u03b3_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_f_326_, lean_object* v_init_327_, lean_object* v_it_328_){
_start:
{
lean_object* v_toApplicative_329_; lean_object* v_toBind_330_; lean_object* v_toFunctor_331_; lean_object* v_toPure_332_; lean_object* v___f_333_; lean_object* v___f_334_; lean_object* v___f_335_; lean_object* v___f_336_; lean_object* v___x_337_; 
v_toApplicative_329_ = lean_ctor_get(v_inst_320_, 0);
lean_inc_ref(v_toApplicative_329_);
v_toBind_330_ = lean_ctor_get(v_inst_320_, 1);
lean_inc(v_toBind_330_);
lean_dec_ref(v_inst_320_);
v_toFunctor_331_ = lean_ctor_get(v_toApplicative_329_, 0);
lean_inc_ref(v_toFunctor_331_);
v_toPure_332_ = lean_ctor_get(v_toApplicative_329_, 1);
lean_inc(v_toPure_332_);
lean_dec_ref(v_toApplicative_329_);
v___f_333_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_334_ = ((lean_object*)(l_Std_Iter_foldM___redArg___closed__0));
v___f_335_ = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__1), 2, 1);
lean_closure_set(v___f_335_, 0, v_toPure_332_);
v___f_336_ = lean_alloc_closure((void*)(l_Std_Iter_foldM___redArg___lam__2), 8, 5);
lean_closure_set(v___f_336_, 0, v_toFunctor_331_);
lean_closure_set(v___f_336_, 1, v_f_326_);
lean_closure_set(v___f_336_, 2, v___f_334_);
lean_closure_set(v___f_336_, 3, v_toBind_330_);
lean_closure_set(v___f_336_, 4, v___f_335_);
v___x_337_ = lean_apply_6(v_inst_325_, v___f_333_, lean_box(0), lean_box(0), v_it_328_, v_init_327_, v___f_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_foldM___boxed(lean_object* v_m_338_, lean_object* v_inst_339_, lean_object* v_00_u03b1_340_, lean_object* v_00_u03b2_341_, lean_object* v_00_u03b3_342_, lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_f_345_, lean_object* v_init_346_, lean_object* v_it_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_Iter_Partial_foldM(v_m_338_, v_inst_339_, v_00_u03b1_340_, v_00_u03b2_341_, v_00_u03b3_342_, v_inst_343_, v_inst_344_, v_f_345_, v_init_346_, v_it_347_);
lean_dec(v_inst_343_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_foldM___redArg(lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_f_351_, lean_object* v_init_352_, lean_object* v_it_353_){
_start:
{
lean_object* v_toApplicative_354_; lean_object* v_toBind_355_; lean_object* v_toFunctor_356_; lean_object* v_toPure_357_; lean_object* v___f_358_; lean_object* v___f_359_; lean_object* v___f_360_; lean_object* v___f_361_; lean_object* v___x_362_; 
v_toApplicative_354_ = lean_ctor_get(v_inst_349_, 0);
lean_inc_ref(v_toApplicative_354_);
v_toBind_355_ = lean_ctor_get(v_inst_349_, 1);
lean_inc(v_toBind_355_);
lean_dec_ref(v_inst_349_);
v_toFunctor_356_ = lean_ctor_get(v_toApplicative_354_, 0);
lean_inc_ref(v_toFunctor_356_);
v_toPure_357_ = lean_ctor_get(v_toApplicative_354_, 1);
lean_inc(v_toPure_357_);
lean_dec_ref(v_toApplicative_354_);
v___f_358_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_359_ = ((lean_object*)(l_Std_Iter_foldM___redArg___closed__0));
v___f_360_ = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__1), 2, 1);
lean_closure_set(v___f_360_, 0, v_toPure_357_);
v___f_361_ = lean_alloc_closure((void*)(l_Std_Iter_foldM___redArg___lam__2), 8, 5);
lean_closure_set(v___f_361_, 0, v_toFunctor_356_);
lean_closure_set(v___f_361_, 1, v_f_351_);
lean_closure_set(v___f_361_, 2, v___f_359_);
lean_closure_set(v___f_361_, 3, v_toBind_355_);
lean_closure_set(v___f_361_, 4, v___f_360_);
v___x_362_ = lean_apply_6(v_inst_350_, v___f_358_, lean_box(0), lean_box(0), v_it_353_, v_init_352_, v___f_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_foldM(lean_object* v_m_363_, lean_object* v_inst_364_, lean_object* v_00_u03b1_365_, lean_object* v_00_u03b2_366_, lean_object* v_00_u03b3_367_, lean_object* v_inst_368_, lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_f_371_, lean_object* v_init_372_, lean_object* v_it_373_){
_start:
{
lean_object* v_toApplicative_374_; lean_object* v_toBind_375_; lean_object* v_toFunctor_376_; lean_object* v_toPure_377_; lean_object* v___f_378_; lean_object* v___f_379_; lean_object* v___f_380_; lean_object* v___f_381_; lean_object* v___x_382_; 
v_toApplicative_374_ = lean_ctor_get(v_inst_364_, 0);
lean_inc_ref(v_toApplicative_374_);
v_toBind_375_ = lean_ctor_get(v_inst_364_, 1);
lean_inc(v_toBind_375_);
lean_dec_ref(v_inst_364_);
v_toFunctor_376_ = lean_ctor_get(v_toApplicative_374_, 0);
lean_inc_ref(v_toFunctor_376_);
v_toPure_377_ = lean_ctor_get(v_toApplicative_374_, 1);
lean_inc(v_toPure_377_);
lean_dec_ref(v_toApplicative_374_);
v___f_378_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_379_ = ((lean_object*)(l_Std_Iter_foldM___redArg___closed__0));
v___f_380_ = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__1), 2, 1);
lean_closure_set(v___f_380_, 0, v_toPure_377_);
v___f_381_ = lean_alloc_closure((void*)(l_Std_Iter_foldM___redArg___lam__2), 8, 5);
lean_closure_set(v___f_381_, 0, v_toFunctor_376_);
lean_closure_set(v___f_381_, 1, v_f_371_);
lean_closure_set(v___f_381_, 2, v___f_379_);
lean_closure_set(v___f_381_, 3, v_toBind_375_);
lean_closure_set(v___f_381_, 4, v___f_380_);
v___x_382_ = lean_apply_6(v_inst_369_, v___f_378_, lean_box(0), lean_box(0), v_it_373_, v_init_372_, v___f_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_foldM___boxed(lean_object* v_m_383_, lean_object* v_inst_384_, lean_object* v_00_u03b1_385_, lean_object* v_00_u03b2_386_, lean_object* v_00_u03b3_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_f_391_, lean_object* v_init_392_, lean_object* v_it_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Std_Iter_Total_foldM(v_m_383_, v_inst_384_, v_00_u03b1_385_, v_00_u03b2_386_, v_00_u03b3_387_, v_inst_388_, v_inst_389_, v_inst_390_, v_f_391_, v_init_392_, v_it_393_);
lean_dec(v_inst_388_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_fold___redArg___lam__1(lean_object* v_f_395_, lean_object* v_x1_396_, lean_object* v_x2_397_, lean_object* v_x3_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_apply_2(v_f_395_, v_x3_398_, v_x1_396_);
v___x_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_fold___redArg(lean_object* v_inst_401_, lean_object* v_f_402_, lean_object* v_init_403_, lean_object* v_it_404_){
_start:
{
lean_object* v___f_405_; lean_object* v___f_406_; lean_object* v___x_407_; 
v___f_405_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_406_ = lean_alloc_closure((void*)(l_Std_Iter_fold___redArg___lam__1), 4, 1);
lean_closure_set(v___f_406_, 0, v_f_402_);
v___x_407_ = lean_apply_6(v_inst_401_, v___f_405_, lean_box(0), lean_box(0), v_it_404_, v_init_403_, v___f_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_fold(lean_object* v_00_u03b1_408_, lean_object* v_00_u03b2_409_, lean_object* v_00_u03b3_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_f_413_, lean_object* v_init_414_, lean_object* v_it_415_){
_start:
{
lean_object* v___f_416_; lean_object* v___f_417_; lean_object* v___x_418_; 
v___f_416_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_417_ = lean_alloc_closure((void*)(l_Std_Iter_fold___redArg___lam__1), 4, 1);
lean_closure_set(v___f_417_, 0, v_f_413_);
v___x_418_ = lean_apply_6(v_inst_412_, v___f_416_, lean_box(0), lean_box(0), v_it_415_, v_init_414_, v___f_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_fold___boxed(lean_object* v_00_u03b1_419_, lean_object* v_00_u03b2_420_, lean_object* v_00_u03b3_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_f_424_, lean_object* v_init_425_, lean_object* v_it_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Std_Iter_fold(v_00_u03b1_419_, v_00_u03b2_420_, v_00_u03b3_421_, v_inst_422_, v_inst_423_, v_f_424_, v_init_425_, v_it_426_);
lean_dec(v_inst_422_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_fold___redArg(lean_object* v_inst_428_, lean_object* v_f_429_, lean_object* v_init_430_, lean_object* v_it_431_){
_start:
{
lean_object* v___f_432_; lean_object* v___f_433_; lean_object* v___x_434_; 
v___f_432_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_433_ = lean_alloc_closure((void*)(l_Std_Iter_fold___redArg___lam__1), 4, 1);
lean_closure_set(v___f_433_, 0, v_f_429_);
v___x_434_ = lean_apply_6(v_inst_428_, v___f_432_, lean_box(0), lean_box(0), v_it_431_, v_init_430_, v___f_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_fold(lean_object* v_00_u03b1_435_, lean_object* v_00_u03b2_436_, lean_object* v_00_u03b3_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_f_440_, lean_object* v_init_441_, lean_object* v_it_442_){
_start:
{
lean_object* v___f_443_; lean_object* v___f_444_; lean_object* v___x_445_; 
v___f_443_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_444_ = lean_alloc_closure((void*)(l_Std_Iter_fold___redArg___lam__1), 4, 1);
lean_closure_set(v___f_444_, 0, v_f_440_);
v___x_445_ = lean_apply_6(v_inst_439_, v___f_443_, lean_box(0), lean_box(0), v_it_442_, v_init_441_, v___f_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_fold___boxed(lean_object* v_00_u03b1_446_, lean_object* v_00_u03b2_447_, lean_object* v_00_u03b3_448_, lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_f_451_, lean_object* v_init_452_, lean_object* v_it_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_Iter_Partial_fold(v_00_u03b1_446_, v_00_u03b2_447_, v_00_u03b3_448_, v_inst_449_, v_inst_450_, v_f_451_, v_init_452_, v_it_453_);
lean_dec(v_inst_449_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_fold___redArg(lean_object* v_inst_455_, lean_object* v_f_456_, lean_object* v_init_457_, lean_object* v_it_458_){
_start:
{
lean_object* v___f_459_; lean_object* v___f_460_; lean_object* v___x_461_; 
v___f_459_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_460_ = lean_alloc_closure((void*)(l_Std_Iter_fold___redArg___lam__1), 4, 1);
lean_closure_set(v___f_460_, 0, v_f_456_);
v___x_461_ = lean_apply_6(v_inst_455_, v___f_459_, lean_box(0), lean_box(0), v_it_458_, v_init_457_, v___f_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_fold(lean_object* v_00_u03b1_462_, lean_object* v_00_u03b2_463_, lean_object* v_00_u03b3_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_f_468_, lean_object* v_init_469_, lean_object* v_it_470_){
_start:
{
lean_object* v___f_471_; lean_object* v___f_472_; lean_object* v___x_473_; 
v___f_471_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_472_ = lean_alloc_closure((void*)(l_Std_Iter_fold___redArg___lam__1), 4, 1);
lean_closure_set(v___f_472_, 0, v_f_468_);
v___x_473_ = lean_apply_6(v_inst_466_, v___f_471_, lean_box(0), lean_box(0), v_it_470_, v_init_469_, v___f_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_fold___boxed(lean_object* v_00_u03b1_474_, lean_object* v_00_u03b2_475_, lean_object* v_00_u03b3_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_f_480_, lean_object* v_init_481_, lean_object* v_it_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_Iter_Total_fold(v_00_u03b1_474_, v_00_u03b2_475_, v_00_u03b3_476_, v_inst_477_, v_inst_478_, v_inst_479_, v_f_480_, v_init_481_, v_it_482_);
lean_dec(v_inst_477_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__1(uint8_t v___x_484_, lean_object* v_toPure_485_, uint8_t v_____do__lift_486_){
_start:
{
if (v_____do__lift_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_box(v___x_484_);
v___x_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
v___x_489_ = lean_apply_2(v_toPure_485_, lean_box(0), v___x_488_);
return v___x_489_;
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = lean_box(v_____do__lift_486_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
v___x_492_ = lean_apply_2(v_toPure_485_, lean_box(0), v___x_491_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__1___boxed(lean_object* v___x_493_, lean_object* v_toPure_494_, lean_object* v_____do__lift_495_){
_start:
{
uint8_t v___x_230__boxed_496_; uint8_t v_____do__lift_231__boxed_497_; lean_object* v_res_498_; 
v___x_230__boxed_496_ = lean_unbox(v___x_493_);
v_____do__lift_231__boxed_497_ = lean_unbox(v_____do__lift_495_);
v_res_498_ = l_Std_Iter_anyM___redArg___lam__1(v___x_230__boxed_496_, v_toPure_494_, v_____do__lift_231__boxed_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__0(lean_object* v_toPure_499_, lean_object* v_____do__lift_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = lean_apply_2(v_toPure_499_, lean_box(0), v_____do__lift_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__2(lean_object* v_p_502_, lean_object* v_toBind_503_, lean_object* v___f_504_, lean_object* v___f_505_, lean_object* v_x1_506_, lean_object* v_x2_507_, uint8_t v_x3_508_){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = lean_apply_1(v_p_502_, v_x1_506_);
lean_inc(v_toBind_503_);
v___x_510_ = lean_apply_4(v_toBind_503_, lean_box(0), lean_box(0), v___x_509_, v___f_504_);
v___x_511_ = lean_apply_4(v_toBind_503_, lean_box(0), lean_box(0), v___x_510_, v___f_505_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__2___boxed(lean_object* v_p_512_, lean_object* v_toBind_513_, lean_object* v___f_514_, lean_object* v___f_515_, lean_object* v_x1_516_, lean_object* v_x2_517_, lean_object* v_x3_518_){
_start:
{
uint8_t v_x3_256__boxed_519_; lean_object* v_res_520_; 
v_x3_256__boxed_519_ = lean_unbox(v_x3_518_);
v_res_520_ = l_Std_Iter_anyM___redArg___lam__2(v_p_512_, v_toBind_513_, v___f_514_, v___f_515_, v_x1_516_, v_x2_517_, v_x3_256__boxed_519_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg(lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_p_523_, lean_object* v_it_524_){
_start:
{
lean_object* v_toApplicative_525_; lean_object* v_toBind_526_; lean_object* v_toPure_527_; lean_object* v___f_528_; uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___f_531_; lean_object* v___f_532_; lean_object* v___f_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_toApplicative_525_ = lean_ctor_get(v_inst_521_, 0);
lean_inc_ref(v_toApplicative_525_);
v_toBind_526_ = lean_ctor_get(v_inst_521_, 1);
lean_inc(v_toBind_526_);
lean_dec_ref(v_inst_521_);
v_toPure_527_ = lean_ctor_get(v_toApplicative_525_, 1);
lean_inc_n(v_toPure_527_, 2);
lean_dec_ref(v_toApplicative_525_);
v___f_528_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_529_ = 0;
v___x_530_ = lean_box(v___x_529_);
v___f_531_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_531_, 0, v___x_530_);
lean_closure_set(v___f_531_, 1, v_toPure_527_);
v___f_532_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_532_, 0, v_toPure_527_);
v___f_533_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_533_, 0, v_p_523_);
lean_closure_set(v___f_533_, 1, v_toBind_526_);
lean_closure_set(v___f_533_, 2, v___f_531_);
lean_closure_set(v___f_533_, 3, v___f_532_);
v___x_534_ = lean_box(v___x_529_);
v___x_535_ = lean_apply_6(v_inst_522_, v___f_528_, lean_box(0), lean_box(0), v_it_524_, v___x_534_, v___f_533_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM(lean_object* v_00_u03b1_536_, lean_object* v_00_u03b2_537_, lean_object* v_m_538_, lean_object* v_inst_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_p_542_, lean_object* v_it_543_){
_start:
{
lean_object* v_toApplicative_544_; lean_object* v_toBind_545_; lean_object* v_toPure_546_; lean_object* v___f_547_; uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___f_550_; lean_object* v___f_551_; lean_object* v___f_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_toApplicative_544_ = lean_ctor_get(v_inst_539_, 0);
lean_inc_ref(v_toApplicative_544_);
v_toBind_545_ = lean_ctor_get(v_inst_539_, 1);
lean_inc(v_toBind_545_);
lean_dec_ref(v_inst_539_);
v_toPure_546_ = lean_ctor_get(v_toApplicative_544_, 1);
lean_inc_n(v_toPure_546_, 2);
lean_dec_ref(v_toApplicative_544_);
v___f_547_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_548_ = 0;
v___x_549_ = lean_box(v___x_548_);
v___f_550_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_550_, 0, v___x_549_);
lean_closure_set(v___f_550_, 1, v_toPure_546_);
v___f_551_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_551_, 0, v_toPure_546_);
v___f_552_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_552_, 0, v_p_542_);
lean_closure_set(v___f_552_, 1, v_toBind_545_);
lean_closure_set(v___f_552_, 2, v___f_550_);
lean_closure_set(v___f_552_, 3, v___f_551_);
v___x_553_ = lean_box(v___x_548_);
v___x_554_ = lean_apply_6(v_inst_541_, v___f_547_, lean_box(0), lean_box(0), v_it_543_, v___x_553_, v___f_552_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___boxed(lean_object* v_00_u03b1_555_, lean_object* v_00_u03b2_556_, lean_object* v_m_557_, lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_p_561_, lean_object* v_it_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Std_Iter_anyM(v_00_u03b1_555_, v_00_u03b2_556_, v_m_557_, v_inst_558_, v_inst_559_, v_inst_560_, v_p_561_, v_it_562_);
lean_dec(v_inst_559_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_anyM___redArg(lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_p_566_, lean_object* v_it_567_){
_start:
{
lean_object* v_toApplicative_568_; lean_object* v_toBind_569_; lean_object* v_toPure_570_; lean_object* v___f_571_; uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___f_574_; lean_object* v___f_575_; lean_object* v___f_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_toApplicative_568_ = lean_ctor_get(v_inst_564_, 0);
lean_inc_ref(v_toApplicative_568_);
v_toBind_569_ = lean_ctor_get(v_inst_564_, 1);
lean_inc(v_toBind_569_);
lean_dec_ref(v_inst_564_);
v_toPure_570_ = lean_ctor_get(v_toApplicative_568_, 1);
lean_inc_n(v_toPure_570_, 2);
lean_dec_ref(v_toApplicative_568_);
v___f_571_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_572_ = 0;
v___x_573_ = lean_box(v___x_572_);
v___f_574_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_574_, 0, v___x_573_);
lean_closure_set(v___f_574_, 1, v_toPure_570_);
v___f_575_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_575_, 0, v_toPure_570_);
v___f_576_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_576_, 0, v_p_566_);
lean_closure_set(v___f_576_, 1, v_toBind_569_);
lean_closure_set(v___f_576_, 2, v___f_574_);
lean_closure_set(v___f_576_, 3, v___f_575_);
v___x_577_ = lean_box(v___x_572_);
v___x_578_ = lean_apply_6(v_inst_565_, v___f_571_, lean_box(0), lean_box(0), v_it_567_, v___x_577_, v___f_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_anyM(lean_object* v_00_u03b1_579_, lean_object* v_00_u03b2_580_, lean_object* v_m_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_p_586_, lean_object* v_it_587_){
_start:
{
lean_object* v_toApplicative_588_; lean_object* v_toBind_589_; lean_object* v_toPure_590_; lean_object* v___f_591_; uint8_t v___x_592_; lean_object* v___x_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_toApplicative_588_ = lean_ctor_get(v_inst_582_, 0);
lean_inc_ref(v_toApplicative_588_);
v_toBind_589_ = lean_ctor_get(v_inst_582_, 1);
lean_inc(v_toBind_589_);
lean_dec_ref(v_inst_582_);
v_toPure_590_ = lean_ctor_get(v_toApplicative_588_, 1);
lean_inc_n(v_toPure_590_, 2);
lean_dec_ref(v_toApplicative_588_);
v___f_591_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_592_ = 0;
v___x_593_ = lean_box(v___x_592_);
v___f_594_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_594_, 0, v___x_593_);
lean_closure_set(v___f_594_, 1, v_toPure_590_);
v___f_595_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_595_, 0, v_toPure_590_);
v___f_596_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_596_, 0, v_p_586_);
lean_closure_set(v___f_596_, 1, v_toBind_589_);
lean_closure_set(v___f_596_, 2, v___f_594_);
lean_closure_set(v___f_596_, 3, v___f_595_);
v___x_597_ = lean_box(v___x_592_);
v___x_598_ = lean_apply_6(v_inst_584_, v___f_591_, lean_box(0), lean_box(0), v_it_587_, v___x_597_, v___f_596_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_anyM___boxed(lean_object* v_00_u03b1_599_, lean_object* v_00_u03b2_600_, lean_object* v_m_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_p_606_, lean_object* v_it_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Std_Iter_Total_anyM(v_00_u03b1_599_, v_00_u03b2_600_, v_m_601_, v_inst_602_, v_inst_603_, v_inst_604_, v_inst_605_, v_p_606_, v_it_607_);
lean_dec(v_inst_603_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_any___redArg___lam__1(lean_object* v_p_609_, uint8_t v___x_610_, lean_object* v_x1_611_, lean_object* v_x2_612_, uint8_t v_x3_613_){
_start:
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_apply_1(v_p_609_, v_x1_611_);
v___x_615_ = lean_unbox(v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_box(v___x_610_);
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
else
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_614_);
return v___x_618_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_any___redArg___lam__1___boxed(lean_object* v_p_619_, lean_object* v___x_620_, lean_object* v_x1_621_, lean_object* v_x2_622_, lean_object* v_x3_623_){
_start:
{
uint8_t v___x_280__boxed_624_; uint8_t v_x3_283__boxed_625_; lean_object* v_res_626_; 
v___x_280__boxed_624_ = lean_unbox(v___x_620_);
v_x3_283__boxed_625_ = lean_unbox(v_x3_623_);
v_res_626_ = l_Std_Iter_any___redArg___lam__1(v_p_619_, v___x_280__boxed_624_, v_x1_621_, v_x2_622_, v_x3_283__boxed_625_);
return v_res_626_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_any___redArg(lean_object* v_inst_627_, lean_object* v_p_628_, lean_object* v_it_629_){
_start:
{
lean_object* v___f_630_; uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___f_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___f_630_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_631_ = 0;
v___x_632_ = lean_box(v___x_631_);
v___f_633_ = lean_alloc_closure((void*)(l_Std_Iter_any___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_633_, 0, v_p_628_);
lean_closure_set(v___f_633_, 1, v___x_632_);
v___x_634_ = lean_box(v___x_631_);
v___x_635_ = lean_apply_6(v_inst_627_, v___f_630_, lean_box(0), lean_box(0), v_it_629_, v___x_634_, v___f_633_);
v___x_636_ = lean_unbox(v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_any___redArg___boxed(lean_object* v_inst_637_, lean_object* v_p_638_, lean_object* v_it_639_){
_start:
{
uint8_t v_res_640_; lean_object* v_r_641_; 
v_res_640_ = l_Std_Iter_any___redArg(v_inst_637_, v_p_638_, v_it_639_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_any(lean_object* v_00_u03b1_642_, lean_object* v_00_u03b2_643_, lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_p_646_, lean_object* v_it_647_){
_start:
{
lean_object* v___f_648_; uint8_t v___x_649_; lean_object* v___x_650_; lean_object* v___f_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___f_648_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_649_ = 0;
v___x_650_ = lean_box(v___x_649_);
v___f_651_ = lean_alloc_closure((void*)(l_Std_Iter_any___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_651_, 0, v_p_646_);
lean_closure_set(v___f_651_, 1, v___x_650_);
v___x_652_ = lean_box(v___x_649_);
v___x_653_ = lean_apply_6(v_inst_645_, v___f_648_, lean_box(0), lean_box(0), v_it_647_, v___x_652_, v___f_651_);
v___x_654_ = lean_unbox(v___x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_any___boxed(lean_object* v_00_u03b1_655_, lean_object* v_00_u03b2_656_, lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_p_659_, lean_object* v_it_660_){
_start:
{
uint8_t v_res_661_; lean_object* v_r_662_; 
v_res_661_ = l_Std_Iter_any(v_00_u03b1_655_, v_00_u03b2_656_, v_inst_657_, v_inst_658_, v_p_659_, v_it_660_);
lean_dec(v_inst_657_);
v_r_662_ = lean_box(v_res_661_);
return v_r_662_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_Total_any___redArg(lean_object* v_inst_663_, lean_object* v_p_664_, lean_object* v_it_665_){
_start:
{
lean_object* v___f_666_; uint8_t v___x_667_; lean_object* v___x_668_; lean_object* v___f_669_; lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___f_666_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_667_ = 0;
v___x_668_ = lean_box(v___x_667_);
v___f_669_ = lean_alloc_closure((void*)(l_Std_Iter_any___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_669_, 0, v_p_664_);
lean_closure_set(v___f_669_, 1, v___x_668_);
v___x_670_ = lean_box(v___x_667_);
v___x_671_ = lean_apply_6(v_inst_663_, v___f_666_, lean_box(0), lean_box(0), v_it_665_, v___x_670_, v___f_669_);
v___x_672_ = lean_unbox(v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_any___redArg___boxed(lean_object* v_inst_673_, lean_object* v_p_674_, lean_object* v_it_675_){
_start:
{
uint8_t v_res_676_; lean_object* v_r_677_; 
v_res_676_ = l_Std_Iter_Total_any___redArg(v_inst_673_, v_p_674_, v_it_675_);
v_r_677_ = lean_box(v_res_676_);
return v_r_677_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_Total_any(lean_object* v_00_u03b1_678_, lean_object* v_00_u03b2_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_p_683_, lean_object* v_it_684_){
_start:
{
lean_object* v___f_685_; uint8_t v___x_686_; lean_object* v___x_687_; lean_object* v___f_688_; lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___f_685_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_686_ = 0;
v___x_687_ = lean_box(v___x_686_);
v___f_688_ = lean_alloc_closure((void*)(l_Std_Iter_any___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_688_, 0, v_p_683_);
lean_closure_set(v___f_688_, 1, v___x_687_);
v___x_689_ = lean_box(v___x_686_);
v___x_690_ = lean_apply_6(v_inst_681_, v___f_685_, lean_box(0), lean_box(0), v_it_684_, v___x_689_, v___f_688_);
v___x_691_ = lean_unbox(v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_any___boxed(lean_object* v_00_u03b1_692_, lean_object* v_00_u03b2_693_, lean_object* v_inst_694_, lean_object* v_inst_695_, lean_object* v_inst_696_, lean_object* v_p_697_, lean_object* v_it_698_){
_start:
{
uint8_t v_res_699_; lean_object* v_r_700_; 
v_res_699_ = l_Std_Iter_Total_any(v_00_u03b1_692_, v_00_u03b2_693_, v_inst_694_, v_inst_695_, v_inst_696_, v_p_697_, v_it_698_);
lean_dec(v_inst_694_);
v_r_700_ = lean_box(v_res_699_);
return v_r_700_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg___lam__1(lean_object* v_toPure_701_, uint8_t v___x_702_, uint8_t v_____do__lift_703_){
_start:
{
if (v_____do__lift_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = lean_box(v_____do__lift_703_);
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
v___x_706_ = lean_apply_2(v_toPure_701_, lean_box(0), v___x_705_);
return v___x_706_;
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = lean_box(v___x_702_);
v___x_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
v___x_709_ = lean_apply_2(v_toPure_701_, lean_box(0), v___x_708_);
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg___lam__1___boxed(lean_object* v_toPure_710_, lean_object* v___x_711_, lean_object* v_____do__lift_712_){
_start:
{
uint8_t v___x_232__boxed_713_; uint8_t v_____do__lift_233__boxed_714_; lean_object* v_res_715_; 
v___x_232__boxed_713_ = lean_unbox(v___x_711_);
v_____do__lift_233__boxed_714_ = lean_unbox(v_____do__lift_712_);
v_res_715_ = l_Std_Iter_allM___redArg___lam__1(v_toPure_710_, v___x_232__boxed_713_, v_____do__lift_233__boxed_714_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg(lean_object* v_inst_716_, lean_object* v_inst_717_, lean_object* v_p_718_, lean_object* v_it_719_){
_start:
{
lean_object* v_toApplicative_720_; lean_object* v_toBind_721_; lean_object* v_toPure_722_; lean_object* v___f_723_; uint8_t v___x_724_; lean_object* v___x_725_; lean_object* v___f_726_; lean_object* v___f_727_; lean_object* v___f_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_toApplicative_720_ = lean_ctor_get(v_inst_716_, 0);
lean_inc_ref(v_toApplicative_720_);
v_toBind_721_ = lean_ctor_get(v_inst_716_, 1);
lean_inc(v_toBind_721_);
lean_dec_ref(v_inst_716_);
v_toPure_722_ = lean_ctor_get(v_toApplicative_720_, 1);
lean_inc_n(v_toPure_722_, 2);
lean_dec_ref(v_toApplicative_720_);
v___f_723_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_724_ = 1;
v___x_725_ = lean_box(v___x_724_);
v___f_726_ = lean_alloc_closure((void*)(l_Std_Iter_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_726_, 0, v_toPure_722_);
lean_closure_set(v___f_726_, 1, v___x_725_);
v___f_727_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_727_, 0, v_toPure_722_);
v___f_728_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_728_, 0, v_p_718_);
lean_closure_set(v___f_728_, 1, v_toBind_721_);
lean_closure_set(v___f_728_, 2, v___f_726_);
lean_closure_set(v___f_728_, 3, v___f_727_);
v___x_729_ = lean_box(v___x_724_);
v___x_730_ = lean_apply_6(v_inst_717_, v___f_723_, lean_box(0), lean_box(0), v_it_719_, v___x_729_, v___f_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_allM(lean_object* v_00_u03b1_731_, lean_object* v_00_u03b2_732_, lean_object* v_m_733_, lean_object* v_inst_734_, lean_object* v_inst_735_, lean_object* v_inst_736_, lean_object* v_p_737_, lean_object* v_it_738_){
_start:
{
lean_object* v_toApplicative_739_; lean_object* v_toBind_740_; lean_object* v_toPure_741_; lean_object* v___f_742_; uint8_t v___x_743_; lean_object* v___x_744_; lean_object* v___f_745_; lean_object* v___f_746_; lean_object* v___f_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_toApplicative_739_ = lean_ctor_get(v_inst_734_, 0);
lean_inc_ref(v_toApplicative_739_);
v_toBind_740_ = lean_ctor_get(v_inst_734_, 1);
lean_inc(v_toBind_740_);
lean_dec_ref(v_inst_734_);
v_toPure_741_ = lean_ctor_get(v_toApplicative_739_, 1);
lean_inc_n(v_toPure_741_, 2);
lean_dec_ref(v_toApplicative_739_);
v___f_742_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_743_ = 1;
v___x_744_ = lean_box(v___x_743_);
v___f_745_ = lean_alloc_closure((void*)(l_Std_Iter_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_745_, 0, v_toPure_741_);
lean_closure_set(v___f_745_, 1, v___x_744_);
v___f_746_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_746_, 0, v_toPure_741_);
v___f_747_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_747_, 0, v_p_737_);
lean_closure_set(v___f_747_, 1, v_toBind_740_);
lean_closure_set(v___f_747_, 2, v___f_745_);
lean_closure_set(v___f_747_, 3, v___f_746_);
v___x_748_ = lean_box(v___x_743_);
v___x_749_ = lean_apply_6(v_inst_736_, v___f_742_, lean_box(0), lean_box(0), v_it_738_, v___x_748_, v___f_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_allM___boxed(lean_object* v_00_u03b1_750_, lean_object* v_00_u03b2_751_, lean_object* v_m_752_, lean_object* v_inst_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_p_756_, lean_object* v_it_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Std_Iter_allM(v_00_u03b1_750_, v_00_u03b2_751_, v_m_752_, v_inst_753_, v_inst_754_, v_inst_755_, v_p_756_, v_it_757_);
lean_dec(v_inst_754_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_allM___redArg(lean_object* v_inst_759_, lean_object* v_inst_760_, lean_object* v_p_761_, lean_object* v_it_762_){
_start:
{
lean_object* v_toApplicative_763_; lean_object* v_toBind_764_; lean_object* v_toPure_765_; lean_object* v___f_766_; uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___f_769_; lean_object* v___f_770_; lean_object* v___f_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_toApplicative_763_ = lean_ctor_get(v_inst_759_, 0);
lean_inc_ref(v_toApplicative_763_);
v_toBind_764_ = lean_ctor_get(v_inst_759_, 1);
lean_inc(v_toBind_764_);
lean_dec_ref(v_inst_759_);
v_toPure_765_ = lean_ctor_get(v_toApplicative_763_, 1);
lean_inc_n(v_toPure_765_, 2);
lean_dec_ref(v_toApplicative_763_);
v___f_766_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_767_ = 1;
v___x_768_ = lean_box(v___x_767_);
v___f_769_ = lean_alloc_closure((void*)(l_Std_Iter_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_769_, 0, v_toPure_765_);
lean_closure_set(v___f_769_, 1, v___x_768_);
v___f_770_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_770_, 0, v_toPure_765_);
v___f_771_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_771_, 0, v_p_761_);
lean_closure_set(v___f_771_, 1, v_toBind_764_);
lean_closure_set(v___f_771_, 2, v___f_769_);
lean_closure_set(v___f_771_, 3, v___f_770_);
v___x_772_ = lean_box(v___x_767_);
v___x_773_ = lean_apply_6(v_inst_760_, v___f_766_, lean_box(0), lean_box(0), v_it_762_, v___x_772_, v___f_771_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_allM(lean_object* v_00_u03b1_774_, lean_object* v_00_u03b2_775_, lean_object* v_m_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_p_781_, lean_object* v_it_782_){
_start:
{
lean_object* v_toApplicative_783_; lean_object* v_toBind_784_; lean_object* v_toPure_785_; lean_object* v___f_786_; uint8_t v___x_787_; lean_object* v___x_788_; lean_object* v___f_789_; lean_object* v___f_790_; lean_object* v___f_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_toApplicative_783_ = lean_ctor_get(v_inst_777_, 0);
lean_inc_ref(v_toApplicative_783_);
v_toBind_784_ = lean_ctor_get(v_inst_777_, 1);
lean_inc(v_toBind_784_);
lean_dec_ref(v_inst_777_);
v_toPure_785_ = lean_ctor_get(v_toApplicative_783_, 1);
lean_inc_n(v_toPure_785_, 2);
lean_dec_ref(v_toApplicative_783_);
v___f_786_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_787_ = 1;
v___x_788_ = lean_box(v___x_787_);
v___f_789_ = lean_alloc_closure((void*)(l_Std_Iter_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_789_, 0, v_toPure_785_);
lean_closure_set(v___f_789_, 1, v___x_788_);
v___f_790_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_790_, 0, v_toPure_785_);
v___f_791_ = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_791_, 0, v_p_781_);
lean_closure_set(v___f_791_, 1, v_toBind_784_);
lean_closure_set(v___f_791_, 2, v___f_789_);
lean_closure_set(v___f_791_, 3, v___f_790_);
v___x_792_ = lean_box(v___x_787_);
v___x_793_ = lean_apply_6(v_inst_779_, v___f_786_, lean_box(0), lean_box(0), v_it_782_, v___x_792_, v___f_791_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_allM___boxed(lean_object* v_00_u03b1_794_, lean_object* v_00_u03b2_795_, lean_object* v_m_796_, lean_object* v_inst_797_, lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_p_801_, lean_object* v_it_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Std_Iter_Total_allM(v_00_u03b1_794_, v_00_u03b2_795_, v_m_796_, v_inst_797_, v_inst_798_, v_inst_799_, v_inst_800_, v_p_801_, v_it_802_);
lean_dec(v_inst_798_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_all___redArg___lam__1(lean_object* v_p_804_, uint8_t v___x_805_, lean_object* v_x1_806_, lean_object* v_x2_807_, uint8_t v_x3_808_){
_start:
{
lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_809_ = lean_apply_1(v_p_804_, v_x1_806_);
v___x_810_ = lean_unbox(v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; 
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_809_);
return v___x_811_;
}
else
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = lean_box(v___x_805_);
v___x_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
return v___x_813_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_all___redArg___lam__1___boxed(lean_object* v_p_814_, lean_object* v___x_815_, lean_object* v_x1_816_, lean_object* v_x2_817_, lean_object* v_x3_818_){
_start:
{
uint8_t v___x_280__boxed_819_; uint8_t v_x3_283__boxed_820_; lean_object* v_res_821_; 
v___x_280__boxed_819_ = lean_unbox(v___x_815_);
v_x3_283__boxed_820_ = lean_unbox(v_x3_818_);
v_res_821_ = l_Std_Iter_all___redArg___lam__1(v_p_814_, v___x_280__boxed_819_, v_x1_816_, v_x2_817_, v_x3_283__boxed_820_);
return v_res_821_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_all___redArg(lean_object* v_inst_822_, lean_object* v_p_823_, lean_object* v_it_824_){
_start:
{
lean_object* v___f_825_; uint8_t v___x_826_; lean_object* v___x_827_; lean_object* v___f_828_; lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v___f_825_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_826_ = 1;
v___x_827_ = lean_box(v___x_826_);
v___f_828_ = lean_alloc_closure((void*)(l_Std_Iter_all___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_828_, 0, v_p_823_);
lean_closure_set(v___f_828_, 1, v___x_827_);
v___x_829_ = lean_box(v___x_826_);
v___x_830_ = lean_apply_6(v_inst_822_, v___f_825_, lean_box(0), lean_box(0), v_it_824_, v___x_829_, v___f_828_);
v___x_831_ = lean_unbox(v___x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_all___redArg___boxed(lean_object* v_inst_832_, lean_object* v_p_833_, lean_object* v_it_834_){
_start:
{
uint8_t v_res_835_; lean_object* v_r_836_; 
v_res_835_ = l_Std_Iter_all___redArg(v_inst_832_, v_p_833_, v_it_834_);
v_r_836_ = lean_box(v_res_835_);
return v_r_836_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_all(lean_object* v_00_u03b1_837_, lean_object* v_00_u03b2_838_, lean_object* v_inst_839_, lean_object* v_inst_840_, lean_object* v_p_841_, lean_object* v_it_842_){
_start:
{
lean_object* v___f_843_; uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___f_846_; lean_object* v___x_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v___f_843_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_844_ = 1;
v___x_845_ = lean_box(v___x_844_);
v___f_846_ = lean_alloc_closure((void*)(l_Std_Iter_all___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_846_, 0, v_p_841_);
lean_closure_set(v___f_846_, 1, v___x_845_);
v___x_847_ = lean_box(v___x_844_);
v___x_848_ = lean_apply_6(v_inst_840_, v___f_843_, lean_box(0), lean_box(0), v_it_842_, v___x_847_, v___f_846_);
v___x_849_ = lean_unbox(v___x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_all___boxed(lean_object* v_00_u03b1_850_, lean_object* v_00_u03b2_851_, lean_object* v_inst_852_, lean_object* v_inst_853_, lean_object* v_p_854_, lean_object* v_it_855_){
_start:
{
uint8_t v_res_856_; lean_object* v_r_857_; 
v_res_856_ = l_Std_Iter_all(v_00_u03b1_850_, v_00_u03b2_851_, v_inst_852_, v_inst_853_, v_p_854_, v_it_855_);
lean_dec(v_inst_852_);
v_r_857_ = lean_box(v_res_856_);
return v_r_857_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_Total_all___redArg(lean_object* v_inst_858_, lean_object* v_p_859_, lean_object* v_it_860_){
_start:
{
lean_object* v___f_861_; uint8_t v___x_862_; lean_object* v___x_863_; lean_object* v___f_864_; lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v___f_861_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_862_ = 1;
v___x_863_ = lean_box(v___x_862_);
v___f_864_ = lean_alloc_closure((void*)(l_Std_Iter_all___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_864_, 0, v_p_859_);
lean_closure_set(v___f_864_, 1, v___x_863_);
v___x_865_ = lean_box(v___x_862_);
v___x_866_ = lean_apply_6(v_inst_858_, v___f_861_, lean_box(0), lean_box(0), v_it_860_, v___x_865_, v___f_864_);
v___x_867_ = lean_unbox(v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_all___redArg___boxed(lean_object* v_inst_868_, lean_object* v_p_869_, lean_object* v_it_870_){
_start:
{
uint8_t v_res_871_; lean_object* v_r_872_; 
v_res_871_ = l_Std_Iter_Total_all___redArg(v_inst_868_, v_p_869_, v_it_870_);
v_r_872_ = lean_box(v_res_871_);
return v_r_872_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_Total_all(lean_object* v_00_u03b1_873_, lean_object* v_00_u03b2_874_, lean_object* v_inst_875_, lean_object* v_inst_876_, lean_object* v_inst_877_, lean_object* v_p_878_, lean_object* v_it_879_){
_start:
{
lean_object* v___f_880_; uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___f_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v___f_880_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_881_ = 1;
v___x_882_ = lean_box(v___x_881_);
v___f_883_ = lean_alloc_closure((void*)(l_Std_Iter_all___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_883_, 0, v_p_878_);
lean_closure_set(v___f_883_, 1, v___x_882_);
v___x_884_ = lean_box(v___x_881_);
v___x_885_ = lean_apply_6(v_inst_876_, v___f_880_, lean_box(0), lean_box(0), v_it_879_, v___x_884_, v___f_883_);
v___x_886_ = lean_unbox(v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_all___boxed(lean_object* v_00_u03b1_887_, lean_object* v_00_u03b2_888_, lean_object* v_inst_889_, lean_object* v_inst_890_, lean_object* v_inst_891_, lean_object* v_p_892_, lean_object* v_it_893_){
_start:
{
uint8_t v_res_894_; lean_object* v_r_895_; 
v_res_894_ = l_Std_Iter_Total_all(v_00_u03b1_887_, v_00_u03b2_888_, v_inst_889_, v_inst_890_, v_inst_891_, v_p_892_, v_it_893_);
lean_dec(v_inst_889_);
v_r_895_ = lean_box(v_res_894_);
return v_r_895_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__1(lean_object* v_toPure_896_, lean_object* v_____do__lift_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = lean_apply_2(v_toPure_896_, lean_box(0), v_____do__lift_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__0(lean_object* v___x_899_, lean_object* v_toPure_900_, lean_object* v_____do__lift_901_){
_start:
{
if (lean_obj_tag(v_____do__lift_901_) == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_899_);
v___x_903_ = lean_apply_2(v_toPure_900_, lean_box(0), v___x_902_);
return v___x_903_;
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; 
lean_dec(v___x_899_);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v_____do__lift_901_);
v___x_905_ = lean_apply_2(v_toPure_900_, lean_box(0), v___x_904_);
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__2(lean_object* v_f_906_, lean_object* v_toBind_907_, lean_object* v___f_908_, lean_object* v___f_909_, lean_object* v_x1_910_, lean_object* v_x2_911_, lean_object* v_x3_912_){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_apply_1(v_f_906_, v_x1_910_);
lean_inc(v_toBind_907_);
v___x_914_ = lean_apply_4(v_toBind_907_, lean_box(0), lean_box(0), v___x_913_, v___f_908_);
v___x_915_ = lean_apply_4(v_toBind_907_, lean_box(0), lean_box(0), v___x_914_, v___f_909_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed(lean_object* v_f_916_, lean_object* v_toBind_917_, lean_object* v___f_918_, lean_object* v___f_919_, lean_object* v_x1_920_, lean_object* v_x2_921_, lean_object* v_x3_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Std_Iter_findSomeM_x3f___redArg___lam__2(v_f_916_, v_toBind_917_, v___f_918_, v___f_919_, v_x1_920_, v_x2_921_, v_x3_922_);
lean_dec(v_x3_922_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg(lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_it_926_, lean_object* v_f_927_){
_start:
{
lean_object* v_toApplicative_928_; lean_object* v_toBind_929_; lean_object* v_toPure_930_; lean_object* v___f_931_; lean_object* v___x_932_; lean_object* v___f_933_; lean_object* v___f_934_; lean_object* v___f_935_; lean_object* v___x_936_; 
v_toApplicative_928_ = lean_ctor_get(v_inst_924_, 0);
lean_inc_ref(v_toApplicative_928_);
v_toBind_929_ = lean_ctor_get(v_inst_924_, 1);
lean_inc(v_toBind_929_);
lean_dec_ref(v_inst_924_);
v_toPure_930_ = lean_ctor_get(v_toApplicative_928_, 1);
lean_inc_n(v_toPure_930_, 2);
lean_dec_ref(v_toApplicative_928_);
v___f_931_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_932_ = lean_box(0);
v___f_933_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_933_, 0, v_toPure_930_);
v___f_934_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_934_, 0, v___x_932_);
lean_closure_set(v___f_934_, 1, v_toPure_930_);
v___f_935_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_935_, 0, v_f_927_);
lean_closure_set(v___f_935_, 1, v_toBind_929_);
lean_closure_set(v___f_935_, 2, v___f_934_);
lean_closure_set(v___f_935_, 3, v___f_933_);
v___x_936_ = lean_apply_6(v_inst_925_, v___f_931_, lean_box(0), lean_box(0), v_it_926_, v___x_932_, v___f_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f(lean_object* v_00_u03b1_937_, lean_object* v_00_u03b2_938_, lean_object* v_00_u03b3_939_, lean_object* v_m_940_, lean_object* v_inst_941_, lean_object* v_inst_942_, lean_object* v_inst_943_, lean_object* v_it_944_, lean_object* v_f_945_){
_start:
{
lean_object* v_toApplicative_946_; lean_object* v_toBind_947_; lean_object* v_toPure_948_; lean_object* v___f_949_; lean_object* v___x_950_; lean_object* v___f_951_; lean_object* v___f_952_; lean_object* v___f_953_; lean_object* v___x_954_; 
v_toApplicative_946_ = lean_ctor_get(v_inst_941_, 0);
lean_inc_ref(v_toApplicative_946_);
v_toBind_947_ = lean_ctor_get(v_inst_941_, 1);
lean_inc(v_toBind_947_);
lean_dec_ref(v_inst_941_);
v_toPure_948_ = lean_ctor_get(v_toApplicative_946_, 1);
lean_inc_n(v_toPure_948_, 2);
lean_dec_ref(v_toApplicative_946_);
v___f_949_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_950_ = lean_box(0);
v___f_951_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_951_, 0, v_toPure_948_);
v___f_952_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_952_, 0, v___x_950_);
lean_closure_set(v___f_952_, 1, v_toPure_948_);
v___f_953_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_953_, 0, v_f_945_);
lean_closure_set(v___f_953_, 1, v_toBind_947_);
lean_closure_set(v___f_953_, 2, v___f_952_);
lean_closure_set(v___f_953_, 3, v___f_951_);
v___x_954_ = lean_apply_6(v_inst_943_, v___f_949_, lean_box(0), lean_box(0), v_it_944_, v___x_950_, v___f_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___boxed(lean_object* v_00_u03b1_955_, lean_object* v_00_u03b2_956_, lean_object* v_00_u03b3_957_, lean_object* v_m_958_, lean_object* v_inst_959_, lean_object* v_inst_960_, lean_object* v_inst_961_, lean_object* v_it_962_, lean_object* v_f_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Std_Iter_findSomeM_x3f(v_00_u03b1_955_, v_00_u03b2_956_, v_00_u03b3_957_, v_m_958_, v_inst_959_, v_inst_960_, v_inst_961_, v_it_962_, v_f_963_);
lean_dec(v_inst_960_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSomeM_x3f___redArg(lean_object* v_inst_965_, lean_object* v_inst_966_, lean_object* v_it_967_, lean_object* v_f_968_){
_start:
{
lean_object* v_toApplicative_969_; lean_object* v_toBind_970_; lean_object* v_toPure_971_; lean_object* v___f_972_; lean_object* v___x_973_; lean_object* v___f_974_; lean_object* v___f_975_; lean_object* v___f_976_; lean_object* v___x_977_; 
v_toApplicative_969_ = lean_ctor_get(v_inst_965_, 0);
lean_inc_ref(v_toApplicative_969_);
v_toBind_970_ = lean_ctor_get(v_inst_965_, 1);
lean_inc(v_toBind_970_);
lean_dec_ref(v_inst_965_);
v_toPure_971_ = lean_ctor_get(v_toApplicative_969_, 1);
lean_inc_n(v_toPure_971_, 2);
lean_dec_ref(v_toApplicative_969_);
v___f_972_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_973_ = lean_box(0);
v___f_974_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_974_, 0, v___x_973_);
lean_closure_set(v___f_974_, 1, v_toPure_971_);
v___f_975_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_975_, 0, v_toPure_971_);
v___f_976_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_976_, 0, v_f_968_);
lean_closure_set(v___f_976_, 1, v_toBind_970_);
lean_closure_set(v___f_976_, 2, v___f_974_);
lean_closure_set(v___f_976_, 3, v___f_975_);
v___x_977_ = lean_apply_6(v_inst_966_, v___f_972_, lean_box(0), lean_box(0), v_it_967_, v___x_973_, v___f_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSomeM_x3f(lean_object* v_00_u03b1_978_, lean_object* v_00_u03b2_979_, lean_object* v_00_u03b3_980_, lean_object* v_m_981_, lean_object* v_inst_982_, lean_object* v_inst_983_, lean_object* v_inst_984_, lean_object* v_it_985_, lean_object* v_f_986_){
_start:
{
lean_object* v_toApplicative_987_; lean_object* v_toBind_988_; lean_object* v_toPure_989_; lean_object* v___f_990_; lean_object* v___x_991_; lean_object* v___f_992_; lean_object* v___f_993_; lean_object* v___f_994_; lean_object* v___x_995_; 
v_toApplicative_987_ = lean_ctor_get(v_inst_982_, 0);
lean_inc_ref(v_toApplicative_987_);
v_toBind_988_ = lean_ctor_get(v_inst_982_, 1);
lean_inc(v_toBind_988_);
lean_dec_ref(v_inst_982_);
v_toPure_989_ = lean_ctor_get(v_toApplicative_987_, 1);
lean_inc_n(v_toPure_989_, 2);
lean_dec_ref(v_toApplicative_987_);
v___f_990_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_991_ = lean_box(0);
v___f_992_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_992_, 0, v___x_991_);
lean_closure_set(v___f_992_, 1, v_toPure_989_);
v___f_993_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_993_, 0, v_toPure_989_);
v___f_994_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_994_, 0, v_f_986_);
lean_closure_set(v___f_994_, 1, v_toBind_988_);
lean_closure_set(v___f_994_, 2, v___f_992_);
lean_closure_set(v___f_994_, 3, v___f_993_);
v___x_995_ = lean_apply_6(v_inst_984_, v___f_990_, lean_box(0), lean_box(0), v_it_985_, v___x_991_, v___f_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSomeM_x3f___boxed(lean_object* v_00_u03b1_996_, lean_object* v_00_u03b2_997_, lean_object* v_00_u03b3_998_, lean_object* v_m_999_, lean_object* v_inst_1000_, lean_object* v_inst_1001_, lean_object* v_inst_1002_, lean_object* v_it_1003_, lean_object* v_f_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Std_Iter_Partial_findSomeM_x3f(v_00_u03b1_996_, v_00_u03b2_997_, v_00_u03b3_998_, v_m_999_, v_inst_1000_, v_inst_1001_, v_inst_1002_, v_it_1003_, v_f_1004_);
lean_dec(v_inst_1001_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f___redArg(lean_object* v_inst_1006_, lean_object* v_inst_1007_, lean_object* v_it_1008_, lean_object* v_f_1009_){
_start:
{
lean_object* v_toApplicative_1010_; lean_object* v_toBind_1011_; lean_object* v_toPure_1012_; lean_object* v___f_1013_; lean_object* v___x_1014_; lean_object* v___f_1015_; lean_object* v___f_1016_; lean_object* v___f_1017_; lean_object* v___x_1018_; 
v_toApplicative_1010_ = lean_ctor_get(v_inst_1006_, 0);
lean_inc_ref(v_toApplicative_1010_);
v_toBind_1011_ = lean_ctor_get(v_inst_1006_, 1);
lean_inc(v_toBind_1011_);
lean_dec_ref(v_inst_1006_);
v_toPure_1012_ = lean_ctor_get(v_toApplicative_1010_, 1);
lean_inc_n(v_toPure_1012_, 2);
lean_dec_ref(v_toApplicative_1010_);
v___f_1013_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1014_ = lean_box(0);
v___f_1015_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1015_, 0, v___x_1014_);
lean_closure_set(v___f_1015_, 1, v_toPure_1012_);
v___f_1016_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1016_, 0, v_toPure_1012_);
v___f_1017_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1017_, 0, v_f_1009_);
lean_closure_set(v___f_1017_, 1, v_toBind_1011_);
lean_closure_set(v___f_1017_, 2, v___f_1015_);
lean_closure_set(v___f_1017_, 3, v___f_1016_);
v___x_1018_ = lean_apply_6(v_inst_1007_, v___f_1013_, lean_box(0), lean_box(0), v_it_1008_, v___x_1014_, v___f_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f(lean_object* v_00_u03b1_1019_, lean_object* v_00_u03b2_1020_, lean_object* v_00_u03b3_1021_, lean_object* v_m_1022_, lean_object* v_inst_1023_, lean_object* v_inst_1024_, lean_object* v_inst_1025_, lean_object* v_inst_1026_, lean_object* v_it_1027_, lean_object* v_f_1028_){
_start:
{
lean_object* v_toApplicative_1029_; lean_object* v_toBind_1030_; lean_object* v_toPure_1031_; lean_object* v___f_1032_; lean_object* v___x_1033_; lean_object* v___f_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___x_1037_; 
v_toApplicative_1029_ = lean_ctor_get(v_inst_1023_, 0);
lean_inc_ref(v_toApplicative_1029_);
v_toBind_1030_ = lean_ctor_get(v_inst_1023_, 1);
lean_inc(v_toBind_1030_);
lean_dec_ref(v_inst_1023_);
v_toPure_1031_ = lean_ctor_get(v_toApplicative_1029_, 1);
lean_inc_n(v_toPure_1031_, 2);
lean_dec_ref(v_toApplicative_1029_);
v___f_1032_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1033_ = lean_box(0);
v___f_1034_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1034_, 0, v___x_1033_);
lean_closure_set(v___f_1034_, 1, v_toPure_1031_);
v___f_1035_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1035_, 0, v_toPure_1031_);
v___f_1036_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1036_, 0, v_f_1028_);
lean_closure_set(v___f_1036_, 1, v_toBind_1030_);
lean_closure_set(v___f_1036_, 2, v___f_1034_);
lean_closure_set(v___f_1036_, 3, v___f_1035_);
v___x_1037_ = lean_apply_6(v_inst_1025_, v___f_1032_, lean_box(0), lean_box(0), v_it_1027_, v___x_1033_, v___f_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f___boxed(lean_object* v_00_u03b1_1038_, lean_object* v_00_u03b2_1039_, lean_object* v_00_u03b3_1040_, lean_object* v_m_1041_, lean_object* v_inst_1042_, lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_inst_1045_, lean_object* v_it_1046_, lean_object* v_f_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Std_Iter_Total_findSomeM_x3f(v_00_u03b1_1038_, v_00_u03b2_1039_, v_00_u03b3_1040_, v_m_1041_, v_inst_1042_, v_inst_1043_, v_inst_1044_, v_inst_1045_, v_it_1046_, v_f_1047_);
lean_dec(v_inst_1043_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg___lam__1(lean_object* v_f_1049_, lean_object* v___x_1050_, lean_object* v_x1_1051_, lean_object* v_x2_1052_, lean_object* v_x3_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_apply_1(v_f_1049_, v_x1_1051_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1050_);
return v___x_1055_;
}
else
{
lean_object* v___x_1056_; 
lean_dec(v___x_1050_);
v___x_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
return v___x_1056_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg___lam__1___boxed(lean_object* v_f_1057_, lean_object* v___x_1058_, lean_object* v_x1_1059_, lean_object* v_x2_1060_, lean_object* v_x3_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Std_Iter_findSome_x3f___redArg___lam__1(v_f_1057_, v___x_1058_, v_x1_1059_, v_x2_1060_, v_x3_1061_);
lean_dec(v_x3_1061_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg(lean_object* v_inst_1063_, lean_object* v_it_1064_, lean_object* v_f_1065_){
_start:
{
lean_object* v___f_1066_; lean_object* v___x_1067_; lean_object* v___f_1068_; lean_object* v___x_1069_; 
v___f_1066_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1067_ = lean_box(0);
v___f_1068_ = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1068_, 0, v_f_1065_);
lean_closure_set(v___f_1068_, 1, v___x_1067_);
v___x_1069_ = lean_apply_6(v_inst_1063_, v___f_1066_, lean_box(0), lean_box(0), v_it_1064_, v___x_1067_, v___f_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f(lean_object* v_00_u03b1_1070_, lean_object* v_00_u03b2_1071_, lean_object* v_00_u03b3_1072_, lean_object* v_inst_1073_, lean_object* v_inst_1074_, lean_object* v_it_1075_, lean_object* v_f_1076_){
_start:
{
lean_object* v___f_1077_; lean_object* v___x_1078_; lean_object* v___f_1079_; lean_object* v___x_1080_; 
v___f_1077_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1078_ = lean_box(0);
v___f_1079_ = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1079_, 0, v_f_1076_);
lean_closure_set(v___f_1079_, 1, v___x_1078_);
v___x_1080_ = lean_apply_6(v_inst_1074_, v___f_1077_, lean_box(0), lean_box(0), v_it_1075_, v___x_1078_, v___f_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___boxed(lean_object* v_00_u03b1_1081_, lean_object* v_00_u03b2_1082_, lean_object* v_00_u03b3_1083_, lean_object* v_inst_1084_, lean_object* v_inst_1085_, lean_object* v_it_1086_, lean_object* v_f_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Std_Iter_findSome_x3f(v_00_u03b1_1081_, v_00_u03b2_1082_, v_00_u03b3_1083_, v_inst_1084_, v_inst_1085_, v_it_1086_, v_f_1087_);
lean_dec(v_inst_1084_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSome_x3f___redArg(lean_object* v_inst_1089_, lean_object* v_it_1090_, lean_object* v_f_1091_){
_start:
{
lean_object* v___f_1092_; lean_object* v___x_1093_; lean_object* v___f_1094_; lean_object* v___x_1095_; 
v___f_1092_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1093_ = lean_box(0);
v___f_1094_ = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1094_, 0, v_f_1091_);
lean_closure_set(v___f_1094_, 1, v___x_1093_);
v___x_1095_ = lean_apply_6(v_inst_1089_, v___f_1092_, lean_box(0), lean_box(0), v_it_1090_, v___x_1093_, v___f_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSome_x3f(lean_object* v_00_u03b1_1096_, lean_object* v_00_u03b2_1097_, lean_object* v_00_u03b3_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_it_1101_, lean_object* v_f_1102_){
_start:
{
lean_object* v___f_1103_; lean_object* v___x_1104_; lean_object* v___f_1105_; lean_object* v___x_1106_; 
v___f_1103_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1104_ = lean_box(0);
v___f_1105_ = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1105_, 0, v_f_1102_);
lean_closure_set(v___f_1105_, 1, v___x_1104_);
v___x_1106_ = lean_apply_6(v_inst_1100_, v___f_1103_, lean_box(0), lean_box(0), v_it_1101_, v___x_1104_, v___f_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSome_x3f___boxed(lean_object* v_00_u03b1_1107_, lean_object* v_00_u03b2_1108_, lean_object* v_00_u03b3_1109_, lean_object* v_inst_1110_, lean_object* v_inst_1111_, lean_object* v_it_1112_, lean_object* v_f_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Std_Iter_Partial_findSome_x3f(v_00_u03b1_1107_, v_00_u03b2_1108_, v_00_u03b3_1109_, v_inst_1110_, v_inst_1111_, v_it_1112_, v_f_1113_);
lean_dec(v_inst_1110_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSome_x3f___redArg(lean_object* v_inst_1115_, lean_object* v_it_1116_, lean_object* v_f_1117_){
_start:
{
lean_object* v___f_1118_; lean_object* v___x_1119_; lean_object* v___f_1120_; lean_object* v___x_1121_; 
v___f_1118_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1119_ = lean_box(0);
v___f_1120_ = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1120_, 0, v_f_1117_);
lean_closure_set(v___f_1120_, 1, v___x_1119_);
v___x_1121_ = lean_apply_6(v_inst_1115_, v___f_1118_, lean_box(0), lean_box(0), v_it_1116_, v___x_1119_, v___f_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSome_x3f(lean_object* v_00_u03b1_1122_, lean_object* v_00_u03b2_1123_, lean_object* v_00_u03b3_1124_, lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_it_1128_, lean_object* v_f_1129_){
_start:
{
lean_object* v___f_1130_; lean_object* v___x_1131_; lean_object* v___f_1132_; lean_object* v___x_1133_; 
v___f_1130_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1131_ = lean_box(0);
v___f_1132_ = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1132_, 0, v_f_1129_);
lean_closure_set(v___f_1132_, 1, v___x_1131_);
v___x_1133_ = lean_apply_6(v_inst_1126_, v___f_1130_, lean_box(0), lean_box(0), v_it_1128_, v___x_1131_, v___f_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSome_x3f___boxed(lean_object* v_00_u03b1_1134_, lean_object* v_00_u03b2_1135_, lean_object* v_00_u03b3_1136_, lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_it_1140_, lean_object* v_f_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Std_Iter_Total_findSome_x3f(v_00_u03b1_1134_, v_00_u03b2_1135_, v_00_u03b3_1136_, v_inst_1137_, v_inst_1138_, v_inst_1139_, v_it_1140_, v_f_1141_);
lean_dec(v_inst_1137_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__3(lean_object* v_toPure_1143_, lean_object* v___x_1144_, lean_object* v_x1_1145_, uint8_t v_____do__lift_1146_){
_start:
{
if (v_____do__lift_1146_ == 0)
{
lean_object* v___x_1147_; 
lean_dec(v_x1_1145_);
v___x_1147_ = lean_apply_2(v_toPure_1143_, lean_box(0), v___x_1144_);
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_dec(v___x_1144_);
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_x1_1145_);
v___x_1149_ = lean_apply_2(v_toPure_1143_, lean_box(0), v___x_1148_);
return v___x_1149_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__3___boxed(lean_object* v_toPure_1150_, lean_object* v___x_1151_, lean_object* v_x1_1152_, lean_object* v_____do__lift_1153_){
_start:
{
uint8_t v_____do__lift_191__boxed_1154_; lean_object* v_res_1155_; 
v_____do__lift_191__boxed_1154_ = lean_unbox(v_____do__lift_1153_);
v_res_1155_ = l_Std_Iter_findM_x3f___redArg___lam__3(v_toPure_1150_, v___x_1151_, v_x1_1152_, v_____do__lift_191__boxed_1154_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__0(lean_object* v_toPure_1156_, lean_object* v___x_1157_, lean_object* v_f_1158_, lean_object* v_toBind_1159_, lean_object* v___f_1160_, lean_object* v___f_1161_, lean_object* v_x1_1162_, lean_object* v_x2_1163_, lean_object* v_x3_1164_){
_start:
{
lean_object* v___f_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_inc(v_x1_1162_);
v___f_1165_ = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_1165_, 0, v_toPure_1156_);
lean_closure_set(v___f_1165_, 1, v___x_1157_);
lean_closure_set(v___f_1165_, 2, v_x1_1162_);
v___x_1166_ = lean_apply_1(v_f_1158_, v_x1_1162_);
lean_inc_n(v_toBind_1159_, 2);
v___x_1167_ = lean_apply_4(v_toBind_1159_, lean_box(0), lean_box(0), v___x_1166_, v___f_1165_);
v___x_1168_ = lean_apply_4(v_toBind_1159_, lean_box(0), lean_box(0), v___x_1167_, v___f_1160_);
v___x_1169_ = lean_apply_4(v_toBind_1159_, lean_box(0), lean_box(0), v___x_1168_, v___f_1161_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_1170_, lean_object* v___x_1171_, lean_object* v_f_1172_, lean_object* v_toBind_1173_, lean_object* v___f_1174_, lean_object* v___f_1175_, lean_object* v_x1_1176_, lean_object* v_x2_1177_, lean_object* v_x3_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Std_Iter_findM_x3f___redArg___lam__0(v_toPure_1170_, v___x_1171_, v_f_1172_, v_toBind_1173_, v___f_1174_, v___f_1175_, v_x1_1176_, v_x2_1177_, v_x3_1178_);
lean_dec(v_x3_1178_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg(lean_object* v_inst_1180_, lean_object* v_inst_1181_, lean_object* v_it_1182_, lean_object* v_f_1183_){
_start:
{
lean_object* v_toApplicative_1184_; lean_object* v_toBind_1185_; lean_object* v_toPure_1186_; lean_object* v___f_1187_; lean_object* v___f_1188_; lean_object* v___x_1189_; lean_object* v___f_1190_; lean_object* v___f_1191_; lean_object* v___x_1192_; 
v_toApplicative_1184_ = lean_ctor_get(v_inst_1180_, 0);
lean_inc_ref(v_toApplicative_1184_);
v_toBind_1185_ = lean_ctor_get(v_inst_1180_, 1);
lean_inc(v_toBind_1185_);
lean_dec_ref(v_inst_1180_);
v_toPure_1186_ = lean_ctor_get(v_toApplicative_1184_, 1);
lean_inc_n(v_toPure_1186_, 3);
lean_dec_ref(v_toApplicative_1184_);
v___f_1187_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_1188_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1188_, 0, v_toPure_1186_);
v___x_1189_ = lean_box(0);
v___f_1190_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1190_, 0, v___x_1189_);
lean_closure_set(v___f_1190_, 1, v_toPure_1186_);
v___f_1191_ = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1191_, 0, v_toPure_1186_);
lean_closure_set(v___f_1191_, 1, v___x_1189_);
lean_closure_set(v___f_1191_, 2, v_f_1183_);
lean_closure_set(v___f_1191_, 3, v_toBind_1185_);
lean_closure_set(v___f_1191_, 4, v___f_1190_);
lean_closure_set(v___f_1191_, 5, v___f_1188_);
v___x_1192_ = lean_apply_6(v_inst_1181_, v___f_1187_, lean_box(0), lean_box(0), v_it_1182_, v___x_1189_, v___f_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f(lean_object* v_00_u03b1_1193_, lean_object* v_00_u03b2_1194_, lean_object* v_m_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_inst_1198_, lean_object* v_it_1199_, lean_object* v_f_1200_){
_start:
{
lean_object* v_toApplicative_1201_; lean_object* v_toBind_1202_; lean_object* v_toPure_1203_; lean_object* v___f_1204_; lean_object* v___f_1205_; lean_object* v___x_1206_; lean_object* v___f_1207_; lean_object* v___f_1208_; lean_object* v___x_1209_; 
v_toApplicative_1201_ = lean_ctor_get(v_inst_1196_, 0);
lean_inc_ref(v_toApplicative_1201_);
v_toBind_1202_ = lean_ctor_get(v_inst_1196_, 1);
lean_inc(v_toBind_1202_);
lean_dec_ref(v_inst_1196_);
v_toPure_1203_ = lean_ctor_get(v_toApplicative_1201_, 1);
lean_inc_n(v_toPure_1203_, 3);
lean_dec_ref(v_toApplicative_1201_);
v___f_1204_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_1205_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1205_, 0, v_toPure_1203_);
v___x_1206_ = lean_box(0);
v___f_1207_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1207_, 0, v___x_1206_);
lean_closure_set(v___f_1207_, 1, v_toPure_1203_);
v___f_1208_ = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1208_, 0, v_toPure_1203_);
lean_closure_set(v___f_1208_, 1, v___x_1206_);
lean_closure_set(v___f_1208_, 2, v_f_1200_);
lean_closure_set(v___f_1208_, 3, v_toBind_1202_);
lean_closure_set(v___f_1208_, 4, v___f_1207_);
lean_closure_set(v___f_1208_, 5, v___f_1205_);
v___x_1209_ = lean_apply_6(v_inst_1198_, v___f_1204_, lean_box(0), lean_box(0), v_it_1199_, v___x_1206_, v___f_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___boxed(lean_object* v_00_u03b1_1210_, lean_object* v_00_u03b2_1211_, lean_object* v_m_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_inst_1215_, lean_object* v_it_1216_, lean_object* v_f_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Std_Iter_findM_x3f(v_00_u03b1_1210_, v_00_u03b2_1211_, v_m_1212_, v_inst_1213_, v_inst_1214_, v_inst_1215_, v_it_1216_, v_f_1217_);
lean_dec(v_inst_1214_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findM_x3f___redArg(lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_it_1221_, lean_object* v_f_1222_){
_start:
{
lean_object* v_toApplicative_1223_; lean_object* v_toBind_1224_; lean_object* v_toPure_1225_; lean_object* v___f_1226_; lean_object* v___f_1227_; lean_object* v___x_1228_; lean_object* v___f_1229_; lean_object* v___f_1230_; lean_object* v___x_1231_; 
v_toApplicative_1223_ = lean_ctor_get(v_inst_1219_, 0);
lean_inc_ref(v_toApplicative_1223_);
v_toBind_1224_ = lean_ctor_get(v_inst_1219_, 1);
lean_inc(v_toBind_1224_);
lean_dec_ref(v_inst_1219_);
v_toPure_1225_ = lean_ctor_get(v_toApplicative_1223_, 1);
lean_inc_n(v_toPure_1225_, 3);
lean_dec_ref(v_toApplicative_1223_);
v___f_1226_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_1227_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1227_, 0, v_toPure_1225_);
v___x_1228_ = lean_box(0);
v___f_1229_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1229_, 0, v___x_1228_);
lean_closure_set(v___f_1229_, 1, v_toPure_1225_);
v___f_1230_ = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1230_, 0, v_toPure_1225_);
lean_closure_set(v___f_1230_, 1, v___x_1228_);
lean_closure_set(v___f_1230_, 2, v_f_1222_);
lean_closure_set(v___f_1230_, 3, v_toBind_1224_);
lean_closure_set(v___f_1230_, 4, v___f_1229_);
lean_closure_set(v___f_1230_, 5, v___f_1227_);
v___x_1231_ = lean_apply_6(v_inst_1220_, v___f_1226_, lean_box(0), lean_box(0), v_it_1221_, v___x_1228_, v___f_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findM_x3f(lean_object* v_00_u03b1_1232_, lean_object* v_00_u03b2_1233_, lean_object* v_m_1234_, lean_object* v_inst_1235_, lean_object* v_inst_1236_, lean_object* v_inst_1237_, lean_object* v_it_1238_, lean_object* v_f_1239_){
_start:
{
lean_object* v_toApplicative_1240_; lean_object* v_toBind_1241_; lean_object* v_toPure_1242_; lean_object* v___f_1243_; lean_object* v___f_1244_; lean_object* v___x_1245_; lean_object* v___f_1246_; lean_object* v___f_1247_; lean_object* v___x_1248_; 
v_toApplicative_1240_ = lean_ctor_get(v_inst_1235_, 0);
lean_inc_ref(v_toApplicative_1240_);
v_toBind_1241_ = lean_ctor_get(v_inst_1235_, 1);
lean_inc(v_toBind_1241_);
lean_dec_ref(v_inst_1235_);
v_toPure_1242_ = lean_ctor_get(v_toApplicative_1240_, 1);
lean_inc_n(v_toPure_1242_, 3);
lean_dec_ref(v_toApplicative_1240_);
v___f_1243_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_1244_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1244_, 0, v_toPure_1242_);
v___x_1245_ = lean_box(0);
v___f_1246_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1246_, 0, v___x_1245_);
lean_closure_set(v___f_1246_, 1, v_toPure_1242_);
v___f_1247_ = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1247_, 0, v_toPure_1242_);
lean_closure_set(v___f_1247_, 1, v___x_1245_);
lean_closure_set(v___f_1247_, 2, v_f_1239_);
lean_closure_set(v___f_1247_, 3, v_toBind_1241_);
lean_closure_set(v___f_1247_, 4, v___f_1246_);
lean_closure_set(v___f_1247_, 5, v___f_1244_);
v___x_1248_ = lean_apply_6(v_inst_1237_, v___f_1243_, lean_box(0), lean_box(0), v_it_1238_, v___x_1245_, v___f_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findM_x3f___boxed(lean_object* v_00_u03b1_1249_, lean_object* v_00_u03b2_1250_, lean_object* v_m_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_inst_1254_, lean_object* v_it_1255_, lean_object* v_f_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Std_Iter_Partial_findM_x3f(v_00_u03b1_1249_, v_00_u03b2_1250_, v_m_1251_, v_inst_1252_, v_inst_1253_, v_inst_1254_, v_it_1255_, v_f_1256_);
lean_dec(v_inst_1253_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f___redArg(lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_it_1260_, lean_object* v_f_1261_){
_start:
{
lean_object* v_toApplicative_1262_; lean_object* v_toBind_1263_; lean_object* v_toPure_1264_; lean_object* v___f_1265_; lean_object* v___f_1266_; lean_object* v___x_1267_; lean_object* v___f_1268_; lean_object* v___f_1269_; lean_object* v___x_1270_; 
v_toApplicative_1262_ = lean_ctor_get(v_inst_1258_, 0);
lean_inc_ref(v_toApplicative_1262_);
v_toBind_1263_ = lean_ctor_get(v_inst_1258_, 1);
lean_inc(v_toBind_1263_);
lean_dec_ref(v_inst_1258_);
v_toPure_1264_ = lean_ctor_get(v_toApplicative_1262_, 1);
lean_inc_n(v_toPure_1264_, 3);
lean_dec_ref(v_toApplicative_1262_);
v___f_1265_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_1266_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1266_, 0, v_toPure_1264_);
v___x_1267_ = lean_box(0);
v___f_1268_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1268_, 0, v___x_1267_);
lean_closure_set(v___f_1268_, 1, v_toPure_1264_);
v___f_1269_ = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1269_, 0, v_toPure_1264_);
lean_closure_set(v___f_1269_, 1, v___x_1267_);
lean_closure_set(v___f_1269_, 2, v_f_1261_);
lean_closure_set(v___f_1269_, 3, v_toBind_1263_);
lean_closure_set(v___f_1269_, 4, v___f_1268_);
lean_closure_set(v___f_1269_, 5, v___f_1266_);
v___x_1270_ = lean_apply_6(v_inst_1259_, v___f_1265_, lean_box(0), lean_box(0), v_it_1260_, v___x_1267_, v___f_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f(lean_object* v_00_u03b1_1271_, lean_object* v_00_u03b2_1272_, lean_object* v_m_1273_, lean_object* v_inst_1274_, lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_inst_1277_, lean_object* v_it_1278_, lean_object* v_f_1279_){
_start:
{
lean_object* v_toApplicative_1280_; lean_object* v_toBind_1281_; lean_object* v_toPure_1282_; lean_object* v___f_1283_; lean_object* v___f_1284_; lean_object* v___x_1285_; lean_object* v___f_1286_; lean_object* v___f_1287_; lean_object* v___x_1288_; 
v_toApplicative_1280_ = lean_ctor_get(v_inst_1274_, 0);
lean_inc_ref(v_toApplicative_1280_);
v_toBind_1281_ = lean_ctor_get(v_inst_1274_, 1);
lean_inc(v_toBind_1281_);
lean_dec_ref(v_inst_1274_);
v_toPure_1282_ = lean_ctor_get(v_toApplicative_1280_, 1);
lean_inc_n(v_toPure_1282_, 3);
lean_dec_ref(v_toApplicative_1280_);
v___f_1283_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___f_1284_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1284_, 0, v_toPure_1282_);
v___x_1285_ = lean_box(0);
v___f_1286_ = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1286_, 0, v___x_1285_);
lean_closure_set(v___f_1286_, 1, v_toPure_1282_);
v___f_1287_ = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1287_, 0, v_toPure_1282_);
lean_closure_set(v___f_1287_, 1, v___x_1285_);
lean_closure_set(v___f_1287_, 2, v_f_1279_);
lean_closure_set(v___f_1287_, 3, v_toBind_1281_);
lean_closure_set(v___f_1287_, 4, v___f_1286_);
lean_closure_set(v___f_1287_, 5, v___f_1284_);
v___x_1288_ = lean_apply_6(v_inst_1276_, v___f_1283_, lean_box(0), lean_box(0), v_it_1278_, v___x_1285_, v___f_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f___boxed(lean_object* v_00_u03b1_1289_, lean_object* v_00_u03b2_1290_, lean_object* v_m_1291_, lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_inst_1294_, lean_object* v_inst_1295_, lean_object* v_it_1296_, lean_object* v_f_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Std_Iter_Total_findM_x3f(v_00_u03b1_1289_, v_00_u03b2_1290_, v_m_1291_, v_inst_1292_, v_inst_1293_, v_inst_1294_, v_inst_1295_, v_it_1296_, v_f_1297_);
lean_dec(v_inst_1293_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg___lam__1(lean_object* v_f_1299_, lean_object* v___x_1300_, lean_object* v_x1_1301_, lean_object* v_x2_1302_, lean_object* v_x3_1303_){
_start:
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
lean_inc(v_x1_1301_);
v___x_1304_ = lean_apply_1(v_f_1299_, v_x1_1301_);
v___x_1305_ = lean_unbox(v___x_1304_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; 
lean_dec(v_x1_1301_);
v___x_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1300_);
return v___x_1306_;
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
lean_dec(v___x_1300_);
v___x_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1307_, 0, v_x1_1301_);
v___x_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
return v___x_1308_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg___lam__1___boxed(lean_object* v_f_1309_, lean_object* v___x_1310_, lean_object* v_x1_1311_, lean_object* v_x2_1312_, lean_object* v_x3_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Std_Iter_find_x3f___redArg___lam__1(v_f_1309_, v___x_1310_, v_x1_1311_, v_x2_1312_, v_x3_1313_);
lean_dec(v_x3_1313_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg(lean_object* v_inst_1315_, lean_object* v_it_1316_, lean_object* v_f_1317_){
_start:
{
lean_object* v___f_1318_; lean_object* v___x_1319_; lean_object* v___f_1320_; lean_object* v___x_1321_; 
v___f_1318_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1319_ = lean_box(0);
v___f_1320_ = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1320_, 0, v_f_1317_);
lean_closure_set(v___f_1320_, 1, v___x_1319_);
v___x_1321_ = lean_apply_6(v_inst_1315_, v___f_1318_, lean_box(0), lean_box(0), v_it_1316_, v___x_1319_, v___f_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f(lean_object* v_00_u03b1_1322_, lean_object* v_00_u03b2_1323_, lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_it_1326_, lean_object* v_f_1327_){
_start:
{
lean_object* v___f_1328_; lean_object* v___x_1329_; lean_object* v___f_1330_; lean_object* v___x_1331_; 
v___f_1328_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1329_ = lean_box(0);
v___f_1330_ = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1330_, 0, v_f_1327_);
lean_closure_set(v___f_1330_, 1, v___x_1329_);
v___x_1331_ = lean_apply_6(v_inst_1325_, v___f_1328_, lean_box(0), lean_box(0), v_it_1326_, v___x_1329_, v___f_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___boxed(lean_object* v_00_u03b1_1332_, lean_object* v_00_u03b2_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_it_1336_, lean_object* v_f_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Std_Iter_find_x3f(v_00_u03b1_1332_, v_00_u03b2_1333_, v_inst_1334_, v_inst_1335_, v_it_1336_, v_f_1337_);
lean_dec(v_inst_1334_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_find_x3f___redArg(lean_object* v_inst_1339_, lean_object* v_it_1340_, lean_object* v_f_1341_){
_start:
{
lean_object* v___f_1342_; lean_object* v___x_1343_; lean_object* v___f_1344_; lean_object* v___x_1345_; 
v___f_1342_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1343_ = lean_box(0);
v___f_1344_ = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1344_, 0, v_f_1341_);
lean_closure_set(v___f_1344_, 1, v___x_1343_);
v___x_1345_ = lean_apply_6(v_inst_1339_, v___f_1342_, lean_box(0), lean_box(0), v_it_1340_, v___x_1343_, v___f_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_find_x3f(lean_object* v_00_u03b1_1346_, lean_object* v_00_u03b2_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_it_1350_, lean_object* v_f_1351_){
_start:
{
lean_object* v___f_1352_; lean_object* v___x_1353_; lean_object* v___f_1354_; lean_object* v___x_1355_; 
v___f_1352_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1353_ = lean_box(0);
v___f_1354_ = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1354_, 0, v_f_1351_);
lean_closure_set(v___f_1354_, 1, v___x_1353_);
v___x_1355_ = lean_apply_6(v_inst_1349_, v___f_1352_, lean_box(0), lean_box(0), v_it_1350_, v___x_1353_, v___f_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_find_x3f___boxed(lean_object* v_00_u03b1_1356_, lean_object* v_00_u03b2_1357_, lean_object* v_inst_1358_, lean_object* v_inst_1359_, lean_object* v_it_1360_, lean_object* v_f_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Std_Iter_Partial_find_x3f(v_00_u03b1_1356_, v_00_u03b2_1357_, v_inst_1358_, v_inst_1359_, v_it_1360_, v_f_1361_);
lean_dec(v_inst_1358_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_find_x3f___redArg(lean_object* v_inst_1363_, lean_object* v_it_1364_, lean_object* v_f_1365_){
_start:
{
lean_object* v___f_1366_; lean_object* v___x_1367_; lean_object* v___f_1368_; lean_object* v___x_1369_; 
v___f_1366_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1367_ = lean_box(0);
v___f_1368_ = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1368_, 0, v_f_1365_);
lean_closure_set(v___f_1368_, 1, v___x_1367_);
v___x_1369_ = lean_apply_6(v_inst_1363_, v___f_1366_, lean_box(0), lean_box(0), v_it_1364_, v___x_1367_, v___f_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_find_x3f(lean_object* v_00_u03b1_1370_, lean_object* v_00_u03b2_1371_, lean_object* v_inst_1372_, lean_object* v_inst_1373_, lean_object* v_inst_1374_, lean_object* v_it_1375_, lean_object* v_f_1376_){
_start:
{
lean_object* v___f_1377_; lean_object* v___x_1378_; lean_object* v___f_1379_; lean_object* v___x_1380_; 
v___f_1377_ = ((lean_object*)(l_Std_Iter_instForIn_x27___redArg___closed__0));
v___x_1378_ = lean_box(0);
v___f_1379_ = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1379_, 0, v_f_1376_);
lean_closure_set(v___f_1379_, 1, v___x_1378_);
v___x_1380_ = lean_apply_6(v_inst_1373_, v___f_1377_, lean_box(0), lean_box(0), v_it_1375_, v___x_1378_, v___f_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_find_x3f___boxed(lean_object* v_00_u03b1_1381_, lean_object* v_00_u03b2_1382_, lean_object* v_inst_1383_, lean_object* v_inst_1384_, lean_object* v_inst_1385_, lean_object* v_it_1386_, lean_object* v_f_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Std_Iter_Total_find_x3f(v_00_u03b1_1381_, v_00_u03b2_1382_, v_inst_1383_, v_inst_1384_, v_inst_1385_, v_it_1386_, v_f_1387_);
lean_dec(v_inst_1383_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___redArg___lam__0(lean_object* v_x_1389_, lean_object* v_x_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_apply_1(v___y_1391_, v___y_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___redArg___lam__1(lean_object* v_b_1394_, lean_object* v_x_1395_, lean_object* v_x_1396_){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_b_1394_);
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___redArg___lam__1___boxed(lean_object* v_b_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Std_Iter_first_x3f___redArg___lam__1(v_b_1399_, v_x_1400_, v_x_1401_);
lean_dec(v_x_1401_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___redArg(lean_object* v_inst_1405_, lean_object* v_it_1406_){
_start:
{
lean_object* v___f_1407_; lean_object* v___f_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___f_1407_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1408_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__1));
v___x_1409_ = lean_box(0);
v___x_1410_ = lean_apply_6(v_inst_1405_, v___f_1407_, lean_box(0), lean_box(0), v_it_1406_, v___x_1409_, v___f_1408_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f(lean_object* v_00_u03b1_1411_, lean_object* v_00_u03b2_1412_, lean_object* v_inst_1413_, lean_object* v_inst_1414_, lean_object* v_it_1415_){
_start:
{
lean_object* v___f_1416_; lean_object* v___f_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___f_1416_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1417_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__1));
v___x_1418_ = lean_box(0);
v___x_1419_ = lean_apply_6(v_inst_1414_, v___f_1416_, lean_box(0), lean_box(0), v_it_1415_, v___x_1418_, v___f_1417_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_first_x3f___boxed(lean_object* v_00_u03b1_1420_, lean_object* v_00_u03b2_1421_, lean_object* v_inst_1422_, lean_object* v_inst_1423_, lean_object* v_it_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Std_Iter_first_x3f(v_00_u03b1_1420_, v_00_u03b2_1421_, v_inst_1422_, v_inst_1423_, v_it_1424_);
lean_dec(v_inst_1422_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_first_x3f___redArg(lean_object* v_inst_1426_, lean_object* v_it_1427_){
_start:
{
lean_object* v___f_1428_; lean_object* v___f_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___f_1428_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1429_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__1));
v___x_1430_ = lean_box(0);
v___x_1431_ = lean_apply_6(v_inst_1426_, v___f_1428_, lean_box(0), lean_box(0), v_it_1427_, v___x_1430_, v___f_1429_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_first_x3f(lean_object* v_00_u03b1_1432_, lean_object* v_00_u03b2_1433_, lean_object* v_inst_1434_, lean_object* v_inst_1435_, lean_object* v_inst_1436_, lean_object* v_it_1437_){
_start:
{
lean_object* v___f_1438_; lean_object* v___f_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___f_1438_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1439_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__1));
v___x_1440_ = lean_box(0);
v___x_1441_ = lean_apply_6(v_inst_1435_, v___f_1438_, lean_box(0), lean_box(0), v_it_1437_, v___x_1440_, v___f_1439_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_first_x3f___boxed(lean_object* v_00_u03b1_1442_, lean_object* v_00_u03b2_1443_, lean_object* v_inst_1444_, lean_object* v_inst_1445_, lean_object* v_inst_1446_, lean_object* v_it_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Std_Iter_Total_first_x3f(v_00_u03b1_1442_, v_00_u03b2_1443_, v_inst_1444_, v_inst_1445_, v_inst_1446_, v_it_1447_);
lean_dec(v_inst_1444_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_isEmpty___redArg___lam__1(lean_object* v_x_1452_, lean_object* v_x_1453_, uint8_t v_x_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = ((lean_object*)(l_Std_Iter_isEmpty___redArg___lam__1___closed__0));
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_isEmpty___redArg___lam__1___boxed(lean_object* v_x_1456_, lean_object* v_x_1457_, lean_object* v_x_1458_){
_start:
{
uint8_t v_x_151__boxed_1459_; lean_object* v_res_1460_; 
v_x_151__boxed_1459_ = lean_unbox(v_x_1458_);
v_res_1460_ = l_Std_Iter_isEmpty___redArg___lam__1(v_x_1456_, v_x_1457_, v_x_151__boxed_1459_);
lean_dec(v_x_1456_);
return v_res_1460_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_isEmpty___redArg(lean_object* v_inst_1462_, lean_object* v_it_1463_){
_start:
{
lean_object* v___f_1464_; lean_object* v___f_1465_; uint8_t v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___f_1464_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1465_ = ((lean_object*)(l_Std_Iter_isEmpty___redArg___closed__0));
v___x_1466_ = 1;
v___x_1467_ = lean_box(v___x_1466_);
v___x_1468_ = lean_apply_6(v_inst_1462_, v___f_1464_, lean_box(0), lean_box(0), v_it_1463_, v___x_1467_, v___f_1465_);
v___x_1469_ = lean_unbox(v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_isEmpty___redArg___boxed(lean_object* v_inst_1470_, lean_object* v_it_1471_){
_start:
{
uint8_t v_res_1472_; lean_object* v_r_1473_; 
v_res_1472_ = l_Std_Iter_isEmpty___redArg(v_inst_1470_, v_it_1471_);
v_r_1473_ = lean_box(v_res_1472_);
return v_r_1473_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_isEmpty(lean_object* v_00_u03b1_1474_, lean_object* v_00_u03b2_1475_, lean_object* v_inst_1476_, lean_object* v_inst_1477_, lean_object* v_it_1478_){
_start:
{
lean_object* v___f_1479_; lean_object* v___f_1480_; uint8_t v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___f_1479_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1480_ = ((lean_object*)(l_Std_Iter_isEmpty___redArg___closed__0));
v___x_1481_ = 1;
v___x_1482_ = lean_box(v___x_1481_);
v___x_1483_ = lean_apply_6(v_inst_1477_, v___f_1479_, lean_box(0), lean_box(0), v_it_1478_, v___x_1482_, v___f_1480_);
v___x_1484_ = lean_unbox(v___x_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_isEmpty___boxed(lean_object* v_00_u03b1_1485_, lean_object* v_00_u03b2_1486_, lean_object* v_inst_1487_, lean_object* v_inst_1488_, lean_object* v_it_1489_){
_start:
{
uint8_t v_res_1490_; lean_object* v_r_1491_; 
v_res_1490_ = l_Std_Iter_isEmpty(v_00_u03b1_1485_, v_00_u03b2_1486_, v_inst_1487_, v_inst_1488_, v_it_1489_);
lean_dec(v_inst_1487_);
v_r_1491_ = lean_box(v_res_1490_);
return v_r_1491_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_Total_isEmpty___redArg(lean_object* v_inst_1492_, lean_object* v_it_1493_){
_start:
{
lean_object* v___f_1494_; lean_object* v___f_1495_; uint8_t v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
v___f_1494_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1495_ = ((lean_object*)(l_Std_Iter_isEmpty___redArg___closed__0));
v___x_1496_ = 1;
v___x_1497_ = lean_box(v___x_1496_);
v___x_1498_ = lean_apply_6(v_inst_1492_, v___f_1494_, lean_box(0), lean_box(0), v_it_1493_, v___x_1497_, v___f_1495_);
v___x_1499_ = lean_unbox(v___x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_isEmpty___redArg___boxed(lean_object* v_inst_1500_, lean_object* v_it_1501_){
_start:
{
uint8_t v_res_1502_; lean_object* v_r_1503_; 
v_res_1502_ = l_Std_Iter_Total_isEmpty___redArg(v_inst_1500_, v_it_1501_);
v_r_1503_ = lean_box(v_res_1502_);
return v_r_1503_;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_Total_isEmpty(lean_object* v_00_u03b1_1504_, lean_object* v_00_u03b2_1505_, lean_object* v_inst_1506_, lean_object* v_inst_1507_, lean_object* v_inst_1508_, lean_object* v_it_1509_){
_start:
{
lean_object* v___f_1510_; lean_object* v___f_1511_; uint8_t v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___f_1510_ = ((lean_object*)(l_Std_Iter_first_x3f___redArg___closed__0));
v___f_1511_ = ((lean_object*)(l_Std_Iter_isEmpty___redArg___closed__0));
v___x_1512_ = 1;
v___x_1513_ = lean_box(v___x_1512_);
v___x_1514_ = lean_apply_6(v_inst_1507_, v___f_1510_, lean_box(0), lean_box(0), v_it_1509_, v___x_1513_, v___f_1511_);
v___x_1515_ = lean_unbox(v___x_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_isEmpty___boxed(lean_object* v_00_u03b1_1516_, lean_object* v_00_u03b2_1517_, lean_object* v_inst_1518_, lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_it_1521_){
_start:
{
uint8_t v_res_1522_; lean_object* v_r_1523_; 
v_res_1522_ = l_Std_Iter_Total_isEmpty(v_00_u03b1_1516_, v_00_u03b2_1517_, v_inst_1518_, v_inst_1519_, v_inst_1520_, v_it_1521_);
lean_dec(v_inst_1518_);
v_r_1523_ = lean_box(v_res_1522_);
return v_r_1523_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_length___redArg___lam__0(lean_object* v_x_1524_, lean_object* v_x_1525_, lean_object* v_f_1526_, lean_object* v_x_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_apply_1(v_f_1526_, v_x_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_length___redArg___lam__1(lean_object* v_x1_1529_, lean_object* v_x2_1530_, lean_object* v_x3_1531_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1532_ = lean_unsigned_to_nat(1u);
v___x_1533_ = lean_nat_add(v_x3_1531_, v___x_1532_);
v___x_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_length___redArg___lam__1___boxed(lean_object* v_x1_1535_, lean_object* v_x2_1536_, lean_object* v_x3_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Std_Iter_length___redArg___lam__1(v_x1_1535_, v_x2_1536_, v_x3_1537_);
lean_dec(v_x3_1537_);
lean_dec(v_x1_1535_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_length___redArg(lean_object* v_inst_1541_, lean_object* v_it_1542_){
_start:
{
lean_object* v___f_1543_; lean_object* v___f_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___f_1543_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__0));
v___f_1544_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__1));
v___x_1545_ = lean_unsigned_to_nat(0u);
v___x_1546_ = lean_apply_6(v_inst_1541_, v___f_1543_, lean_box(0), lean_box(0), v_it_1542_, v___x_1545_, v___f_1544_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_length(lean_object* v_00_u03b1_1547_, lean_object* v_00_u03b2_1548_, lean_object* v_inst_1549_, lean_object* v_inst_1550_, lean_object* v_it_1551_){
_start:
{
lean_object* v___f_1552_; lean_object* v___f_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___f_1552_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__0));
v___f_1553_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__1));
v___x_1554_ = lean_unsigned_to_nat(0u);
v___x_1555_ = lean_apply_6(v_inst_1550_, v___f_1552_, lean_box(0), lean_box(0), v_it_1551_, v___x_1554_, v___f_1553_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_length___boxed(lean_object* v_00_u03b1_1556_, lean_object* v_00_u03b2_1557_, lean_object* v_inst_1558_, lean_object* v_inst_1559_, lean_object* v_it_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Std_Iter_length(v_00_u03b1_1556_, v_00_u03b2_1557_, v_inst_1558_, v_inst_1559_, v_it_1560_);
lean_dec(v_inst_1558_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_count___redArg(lean_object* v_inst_1562_, lean_object* v_it_1563_){
_start:
{
lean_object* v___f_1564_; lean_object* v___f_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___f_1564_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__0));
v___f_1565_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__1));
v___x_1566_ = lean_unsigned_to_nat(0u);
v___x_1567_ = lean_apply_6(v_inst_1562_, v___f_1564_, lean_box(0), lean_box(0), v_it_1563_, v___x_1566_, v___f_1565_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_count(lean_object* v_00_u03b1_1568_, lean_object* v_00_u03b2_1569_, lean_object* v_inst_1570_, lean_object* v_inst_1571_, lean_object* v_it_1572_){
_start:
{
lean_object* v___f_1573_; lean_object* v___f_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___f_1573_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__0));
v___f_1574_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__1));
v___x_1575_ = lean_unsigned_to_nat(0u);
v___x_1576_ = lean_apply_6(v_inst_1571_, v___f_1573_, lean_box(0), lean_box(0), v_it_1572_, v___x_1575_, v___f_1574_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_count___boxed(lean_object* v_00_u03b1_1577_, lean_object* v_00_u03b2_1578_, lean_object* v_inst_1579_, lean_object* v_inst_1580_, lean_object* v_it_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Std_Iter_count(v_00_u03b1_1577_, v_00_u03b2_1578_, v_inst_1579_, v_inst_1580_, v_it_1581_);
lean_dec(v_inst_1579_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_size___redArg(lean_object* v_inst_1583_, lean_object* v_it_1584_){
_start:
{
lean_object* v___f_1585_; lean_object* v___f_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___f_1585_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__0));
v___f_1586_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__1));
v___x_1587_ = lean_unsigned_to_nat(0u);
v___x_1588_ = lean_apply_6(v_inst_1583_, v___f_1585_, lean_box(0), lean_box(0), v_it_1584_, v___x_1587_, v___f_1586_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_size(lean_object* v_00_u03b1_1589_, lean_object* v_00_u03b2_1590_, lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_it_1593_){
_start:
{
lean_object* v___f_1594_; lean_object* v___f_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___f_1594_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__0));
v___f_1595_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__1));
v___x_1596_ = lean_unsigned_to_nat(0u);
v___x_1597_ = lean_apply_6(v_inst_1592_, v___f_1594_, lean_box(0), lean_box(0), v_it_1593_, v___x_1596_, v___f_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_size___boxed(lean_object* v_00_u03b1_1598_, lean_object* v_00_u03b2_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_it_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Std_Iter_size(v_00_u03b1_1598_, v_00_u03b2_1599_, v_inst_1600_, v_inst_1601_, v_it_1602_);
lean_dec(v_inst_1600_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_count___redArg(lean_object* v_inst_1604_, lean_object* v_it_1605_){
_start:
{
lean_object* v___f_1606_; lean_object* v___f_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___f_1606_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__0));
v___f_1607_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__1));
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = lean_apply_6(v_inst_1604_, v___f_1606_, lean_box(0), lean_box(0), v_it_1605_, v___x_1608_, v___f_1607_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_count(lean_object* v_00_u03b1_1610_, lean_object* v_00_u03b2_1611_, lean_object* v_inst_1612_, lean_object* v_inst_1613_, lean_object* v_it_1614_){
_start:
{
lean_object* v___f_1615_; lean_object* v___f_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___f_1615_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__0));
v___f_1616_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__1));
v___x_1617_ = lean_unsigned_to_nat(0u);
v___x_1618_ = lean_apply_6(v_inst_1613_, v___f_1615_, lean_box(0), lean_box(0), v_it_1614_, v___x_1617_, v___f_1616_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_count___boxed(lean_object* v_00_u03b1_1619_, lean_object* v_00_u03b2_1620_, lean_object* v_inst_1621_, lean_object* v_inst_1622_, lean_object* v_it_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Std_Iter_Partial_count(v_00_u03b1_1619_, v_00_u03b2_1620_, v_inst_1621_, v_inst_1622_, v_it_1623_);
lean_dec(v_inst_1621_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_size___redArg(lean_object* v_inst_1625_, lean_object* v_it_1626_){
_start:
{
lean_object* v___f_1627_; lean_object* v___f_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___f_1627_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__0));
v___f_1628_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__1));
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = lean_apply_6(v_inst_1625_, v___f_1627_, lean_box(0), lean_box(0), v_it_1626_, v___x_1629_, v___f_1628_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_size(lean_object* v_00_u03b1_1631_, lean_object* v_00_u03b2_1632_, lean_object* v_inst_1633_, lean_object* v_inst_1634_, lean_object* v_it_1635_){
_start:
{
lean_object* v___f_1636_; lean_object* v___f_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___f_1636_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__0));
v___f_1637_ = ((lean_object*)(l_Std_Iter_length___redArg___closed__1));
v___x_1638_ = lean_unsigned_to_nat(0u);
v___x_1639_ = lean_apply_6(v_inst_1634_, v___f_1636_, lean_box(0), lean_box(0), v_it_1635_, v___x_1638_, v___f_1637_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_size___boxed(lean_object* v_00_u03b1_1640_, lean_object* v_00_u03b2_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_it_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Std_Iter_Partial_size(v_00_u03b1_1640_, v_00_u03b2_1641_, v_inst_1642_, v_inst_1643_, v_it_1644_);
lean_dec(v_inst_1642_);
return v_res_1645_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Partial(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Total(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
