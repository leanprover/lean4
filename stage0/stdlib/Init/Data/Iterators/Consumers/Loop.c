// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Loop
// Imports: public import Init.Data.Iterators.Consumers.Collect public import Init.Data.Iterators.Consumers.Monadic.Loop
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
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_instForIn_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_count___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_instForIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSome_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_size(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSome_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Iter_foldM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_anyM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_count___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_count___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_any___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Iter_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_any___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_count(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Iter_Total_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Iter_count___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_instForMPartialOfIteratorLoopIdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_count(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Iter_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_fold___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_instForIn_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInPartialOfMonadOfIteratorLoopId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_instForIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__1(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Iter_Total_instForIn_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSome_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_allM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_allM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Iter_all___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_allM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInPartialOfMonadOfIteratorLoopId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_count___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSomeM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_size(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_all___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMPartialOfIteratorLoopIdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_count___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_all___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Iter_Total_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Iter_Total_all___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_foldM___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_instForIn_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_anyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_anyM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Iter_any___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_any___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_all___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_count___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInIterOfMonadOfIteratorLoopId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_anyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_anyM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Iter_count___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_size___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg___lam__1(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSomeM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Iter_Total_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSome_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInPartialOfMonadOfIteratorLoopId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Iter_foldM___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Iter_Total_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInIterOfMonadOfIteratorLoopId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_allM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_all___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_allM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_any___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_instForInIterOfMonadOfIteratorLoopId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_size___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_count___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMPartialOfIteratorLoopIdOfMonad___redArg(lean_object*, lean_object*);
static lean_object* l_Std_Iter_instForIn_x27___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_Iter_Total_any___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_3(x_1, x_4, lean_box(0), x_6);
x_8 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__1), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__2), 6, 3);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_9);
lean_closure_set(x_12, 2, x_11);
x_13 = lean_apply_6(x_2, x_3, lean_box(0), lean_box(0), x_5, x_6, x_12);
return x_13;
}
}
static lean_object* _init_l_Std_Iter_instForIn_x27___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__0), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_4 = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__3), 7, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_8 = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__3), 7, 3);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_instForIn_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Iter_instForIn_x27(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_instForInIterOfMonadOfIteratorLoopId___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_4 = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__3), 7, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
x_5 = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_instForInIterOfMonadOfIteratorLoopId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_instForInIterOfMonadOfIteratorLoopId___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_instForInIterOfMonadOfIteratorLoopId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_instForInIterOfMonadOfIteratorLoopId(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_instForIn_x27___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_4 = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__3), 7, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_instForIn_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_8 = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__3), 7, 3);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_instForIn_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Iter_Partial_instForIn_x27(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_instForInPartialOfMonadOfIteratorLoopId___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_4 = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__3), 7, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
x_5 = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_instForInPartialOfMonadOfIteratorLoopId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_instForInPartialOfMonadOfIteratorLoopId___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_instForInPartialOfMonadOfIteratorLoopId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_instForInPartialOfMonadOfIteratorLoopId(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_instForIn_x27___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_4 = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__3), 7, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_instForIn_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_9 = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__3), 7, 3);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_6);
lean_closure_set(x_9, 2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_instForIn_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Iter_Total_instForIn_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_4 = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__3), 7, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
x_5 = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId___redArg(x_4, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_apply_1(x_1, x_5);
lean_inc(x_2);
x_9 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_8, x_3);
x_10 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_9, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = lean_alloc_closure((void*)(l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__0), 3, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
x_10 = lean_alloc_closure((void*)(l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__2), 7, 4);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_9);
lean_closure_set(x_10, 3, x_3);
x_11 = lean_apply_6(x_4, x_5, lean_box(0), lean_box(0), x_6, x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Std_Iter_instForIn_x27___redArg___closed__0;
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = lean_alloc_closure((void*)(l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__3), 7, 5);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_1);
lean_closure_set(x_8, 4, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_instForMIterOfIteratorLoopIdOfMonad___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_instForMIterOfIteratorLoopIdOfMonad(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_instForMPartialOfIteratorLoopIdOfMonad___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Std_Iter_instForIn_x27___redArg___closed__0;
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = lean_alloc_closure((void*)(l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__3), 7, 5);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_1);
lean_closure_set(x_8, 4, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_instForMPartialOfIteratorLoopIdOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_instForMPartialOfIteratorLoopIdOfMonad___redArg(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_instForMPartialOfIteratorLoopIdOfMonad___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_instForMPartialOfIteratorLoopIdOfMonad(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Std_Iter_instForIn_x27___redArg___closed__0;
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = lean_alloc_closure((void*)(l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__3), 7, 5);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_2);
lean_closure_set(x_8, 4, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId___redArg(x_4, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_foldM___redArg___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_foldM___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_apply_2(x_2, x_8, x_6);
x_11 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_3, x_10);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_11, x_5);
return x_12;
}
}
static lean_object* _init_l_Std_Iter_foldM___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Iter_foldM___redArg___lam__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_foldM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_11 = l_Std_Iter_foldM___redArg___closed__0;
x_12 = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__1), 2, 1);
lean_closure_set(x_12, 0, x_9);
x_13 = lean_alloc_closure((void*)(l_Std_Iter_foldM___redArg___lam__2), 8, 5);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_apply_6(x_2, x_10, lean_box(0), lean_box(0), x_5, x_4, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
x_13 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec_ref(x_11);
x_15 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_16 = l_Std_Iter_foldM___redArg___closed__0;
x_17 = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__1), 2, 1);
lean_closure_set(x_17, 0, x_14);
x_18 = lean_alloc_closure((void*)(l_Std_Iter_foldM___redArg___lam__2), 8, 5);
lean_closure_set(x_18, 0, x_13);
lean_closure_set(x_18, 1, x_8);
lean_closure_set(x_18, 2, x_16);
lean_closure_set(x_18, 3, x_12);
lean_closure_set(x_18, 4, x_17);
x_19 = lean_apply_6(x_7, x_15, lean_box(0), lean_box(0), x_10, x_9, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_foldM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Iter_foldM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_foldM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_11 = l_Std_Iter_foldM___redArg___closed__0;
x_12 = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__1), 2, 1);
lean_closure_set(x_12, 0, x_9);
x_13 = lean_alloc_closure((void*)(l_Std_Iter_foldM___redArg___lam__2), 8, 5);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_apply_6(x_2, x_10, lean_box(0), lean_box(0), x_5, x_4, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
x_13 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec_ref(x_11);
x_15 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_16 = l_Std_Iter_foldM___redArg___closed__0;
x_17 = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__1), 2, 1);
lean_closure_set(x_17, 0, x_14);
x_18 = lean_alloc_closure((void*)(l_Std_Iter_foldM___redArg___lam__2), 8, 5);
lean_closure_set(x_18, 0, x_13);
lean_closure_set(x_18, 1, x_8);
lean_closure_set(x_18, 2, x_16);
lean_closure_set(x_18, 3, x_12);
lean_closure_set(x_18, 4, x_17);
x_19 = lean_apply_6(x_7, x_15, lean_box(0), lean_box(0), x_10, x_9, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_foldM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Iter_Partial_foldM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_foldM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_11 = l_Std_Iter_foldM___redArg___closed__0;
x_12 = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__1), 2, 1);
lean_closure_set(x_12, 0, x_9);
x_13 = lean_alloc_closure((void*)(l_Std_Iter_foldM___redArg___lam__2), 8, 5);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_7);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_apply_6(x_2, x_10, lean_box(0), lean_box(0), x_5, x_4, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec_ref(x_2);
x_14 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_17 = l_Std_Iter_foldM___redArg___closed__0;
x_18 = lean_alloc_closure((void*)(l_Std_Iter_instForIn_x27___redArg___lam__1), 2, 1);
lean_closure_set(x_18, 0, x_15);
x_19 = lean_alloc_closure((void*)(l_Std_Iter_foldM___redArg___lam__2), 8, 5);
lean_closure_set(x_19, 0, x_14);
lean_closure_set(x_19, 1, x_9);
lean_closure_set(x_19, 2, x_17);
lean_closure_set(x_19, 3, x_13);
lean_closure_set(x_19, 4, x_18);
x_20 = lean_apply_6(x_7, x_16, lean_box(0), lean_box(0), x_11, x_10, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_foldM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Iter_Total_foldM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_fold___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_2(x_1, x_4, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_fold___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_6 = lean_alloc_closure((void*)(l_Std_Iter_fold___redArg___lam__1), 4, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_apply_6(x_1, x_5, lean_box(0), lean_box(0), x_4, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_10 = lean_alloc_closure((void*)(l_Std_Iter_fold___redArg___lam__1), 4, 1);
lean_closure_set(x_10, 0, x_6);
x_11 = lean_apply_6(x_5, x_9, lean_box(0), lean_box(0), x_8, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_fold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Iter_fold(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_fold___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_6 = lean_alloc_closure((void*)(l_Std_Iter_fold___redArg___lam__1), 4, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_apply_6(x_1, x_5, lean_box(0), lean_box(0), x_4, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_10 = lean_alloc_closure((void*)(l_Std_Iter_fold___redArg___lam__1), 4, 1);
lean_closure_set(x_10, 0, x_6);
x_11 = lean_apply_6(x_5, x_9, lean_box(0), lean_box(0), x_8, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_fold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Iter_Partial_fold(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_fold___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_6 = lean_alloc_closure((void*)(l_Std_Iter_fold___redArg___lam__1), 4, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_apply_6(x_1, x_5, lean_box(0), lean_box(0), x_4, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_11 = lean_alloc_closure((void*)(l_Std_Iter_fold___redArg___lam__1), 4, 1);
lean_closure_set(x_11, 0, x_7);
x_12 = lean_apply_6(x_5, x_10, lean_box(0), lean_box(0), x_9, x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_fold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Iter_Total_fold(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__1(uint8_t x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_3);
x_6 = l_Std_Iter_anyM___redArg___lam__1(x_4, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_apply_1(x_1, x_5);
lean_inc(x_2);
x_9 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_8, x_3);
x_10 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_9, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
x_9 = l_Std_Iter_anyM___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_9 = 0;
x_10 = lean_box(x_9);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(x_12, 0, x_7);
x_13 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_box(x_9);
x_15 = lean_apply_6(x_2, x_8, lean_box(0), lean_box(0), x_4, x_14, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec_ref(x_4);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_13 = 0;
x_14 = lean_box(x_13);
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_11);
x_16 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(x_16, 0, x_11);
x_17 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_17, 0, x_7);
lean_closure_set(x_17, 1, x_10);
lean_closure_set(x_17, 2, x_15);
lean_closure_set(x_17, 3, x_16);
x_18 = lean_box(x_13);
x_19 = lean_apply_6(x_6, x_12, lean_box(0), lean_box(0), x_8, x_18, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_anyM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Iter_anyM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_anyM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_9 = 0;
x_10 = lean_box(x_9);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(x_12, 0, x_7);
x_13 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_box(x_9);
x_15 = lean_apply_6(x_2, x_8, lean_box(0), lean_box(0), x_4, x_14, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_anyM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_14 = 0;
x_15 = lean_box(x_14);
lean_inc(x_12);
x_16 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_12);
x_17 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(x_17, 0, x_12);
x_18 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_18, 0, x_8);
lean_closure_set(x_18, 1, x_11);
lean_closure_set(x_18, 2, x_16);
lean_closure_set(x_18, 3, x_17);
x_19 = lean_box(x_14);
x_20 = lean_apply_6(x_6, x_13, lean_box(0), lean_box(0), x_9, x_19, x_18);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_anyM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Iter_Total_anyM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_any___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_apply_1(x_1, x_3);
x_7 = lean_unbox(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_any___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_5);
x_8 = l_Std_Iter_any___redArg___lam__1(x_1, x_6, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_any___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_5 = 0;
x_6 = lean_box(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_Iter_any___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_box(x_5);
x_9 = lean_apply_6(x_1, x_4, lean_box(0), lean_box(0), x_3, x_8, x_7);
x_10 = lean_unbox(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_any___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Iter_any___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_any(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_closure((void*)(l_Std_Iter_any___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_10, 0, x_5);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_box(x_8);
x_12 = lean_apply_6(x_4, x_7, lean_box(0), lean_box(0), x_6, x_11, x_10);
x_13 = lean_unbox(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_any___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Std_Iter_any(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_Total_any___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_5 = 0;
x_6 = lean_box(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_Iter_any___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_box(x_5);
x_9 = lean_apply_6(x_1, x_4, lean_box(0), lean_box(0), x_3, x_8, x_7);
x_10 = lean_unbox(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_any___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Iter_Total_any___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_Total_any(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_closure((void*)(l_Std_Iter_any___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_11, 0, x_6);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_box(x_9);
x_13 = lean_apply_6(x_4, x_8, lean_box(0), lean_box(0), x_7, x_12, x_11);
x_14 = lean_unbox(x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_any___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Std_Iter_Total_any(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg___lam__1(lean_object* x_1, uint8_t x_2, uint8_t x_3) {
_start:
{
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
x_5 = lean_unbox(x_3);
x_6 = l_Std_Iter_allM___redArg___lam__1(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_allM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_9 = 1;
x_10 = lean_box(x_9);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Std_Iter_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(x_12, 0, x_7);
x_13 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_box(x_9);
x_15 = lean_apply_6(x_2, x_8, lean_box(0), lean_box(0), x_4, x_14, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_allM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec_ref(x_4);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_13 = 1;
x_14 = lean_box(x_13);
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l_Std_Iter_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(x_16, 0, x_11);
x_17 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_17, 0, x_7);
lean_closure_set(x_17, 1, x_10);
lean_closure_set(x_17, 2, x_15);
lean_closure_set(x_17, 3, x_16);
x_18 = lean_box(x_13);
x_19 = lean_apply_6(x_6, x_12, lean_box(0), lean_box(0), x_8, x_18, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_allM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Iter_allM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_allM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_9 = 1;
x_10 = lean_box(x_9);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Std_Iter_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(x_12, 0, x_7);
x_13 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_box(x_9);
x_15 = lean_apply_6(x_2, x_8, lean_box(0), lean_box(0), x_4, x_14, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_allM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_14 = 1;
x_15 = lean_box(x_14);
lean_inc(x_12);
x_16 = lean_alloc_closure((void*)(l_Std_Iter_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_16, 0, x_12);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__0), 2, 1);
lean_closure_set(x_17, 0, x_12);
x_18 = lean_alloc_closure((void*)(l_Std_Iter_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_18, 0, x_8);
lean_closure_set(x_18, 1, x_11);
lean_closure_set(x_18, 2, x_16);
lean_closure_set(x_18, 3, x_17);
x_19 = lean_box(x_14);
x_20 = lean_apply_6(x_6, x_13, lean_box(0), lean_box(0), x_9, x_19, x_18);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_allM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Iter_Total_allM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_all___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_apply_1(x_1, x_3);
x_7 = lean_unbox(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_all___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_5);
x_8 = l_Std_Iter_all___redArg___lam__1(x_1, x_6, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_all___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_5 = 1;
x_6 = lean_box(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_Iter_all___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_box(x_5);
x_9 = lean_apply_6(x_1, x_4, lean_box(0), lean_box(0), x_3, x_8, x_7);
x_10 = lean_unbox(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_all___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Iter_all___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_all(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_alloc_closure((void*)(l_Std_Iter_all___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_10, 0, x_5);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_box(x_8);
x_12 = lean_apply_6(x_4, x_7, lean_box(0), lean_box(0), x_6, x_11, x_10);
x_13 = lean_unbox(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_all___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Std_Iter_all(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_Total_all___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_5 = 1;
x_6 = lean_box(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_Iter_all___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_box(x_5);
x_9 = lean_apply_6(x_1, x_4, lean_box(0), lean_box(0), x_3, x_8, x_7);
x_10 = lean_unbox(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_all___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Iter_Total_all___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Iter_Total_all(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_closure((void*)(l_Std_Iter_all___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_11, 0, x_6);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_box(x_9);
x_13 = lean_apply_6(x_4, x_8, lean_box(0), lean_box(0), x_7, x_12, x_11);
x_14 = lean_unbox(x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_all___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Std_Iter_Total_all(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_3);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_apply_1(x_1, x_5);
lean_inc(x_2);
x_9 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_8, x_3);
x_10 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_9, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Iter_findSomeM_x3f___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_9 = lean_box(0);
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_10, 0, x_7);
x_11 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_10);
x_13 = lean_apply_6(x_2, x_8, lean_box(0), lean_box(0), x_3, x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec_ref(x_5);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_14 = lean_box(0);
lean_inc(x_12);
x_15 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_15, 0, x_12);
x_16 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_12);
x_17 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_17, 0, x_9);
lean_closure_set(x_17, 1, x_11);
lean_closure_set(x_17, 2, x_16);
lean_closure_set(x_17, 3, x_15);
x_18 = lean_apply_6(x_7, x_13, lean_box(0), lean_box(0), x_8, x_14, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSomeM_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Iter_findSomeM_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSomeM_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_9 = lean_box(0);
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_7);
x_11 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_11, 0, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_11);
x_13 = lean_apply_6(x_2, x_8, lean_box(0), lean_box(0), x_3, x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSomeM_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec_ref(x_5);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_14 = lean_box(0);
lean_inc(x_12);
x_15 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_12);
x_16 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_16, 0, x_12);
x_17 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_17, 0, x_9);
lean_closure_set(x_17, 1, x_11);
lean_closure_set(x_17, 2, x_15);
lean_closure_set(x_17, 3, x_16);
x_18 = lean_apply_6(x_7, x_13, lean_box(0), lean_box(0), x_8, x_14, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSomeM_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Iter_Partial_findSomeM_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_9 = lean_box(0);
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_7);
x_11 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_11, 0, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_11);
x_13 = lean_apply_6(x_2, x_8, lean_box(0), lean_box(0), x_3, x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec_ref(x_5);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_15 = lean_box(0);
lean_inc(x_13);
x_16 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_13);
x_17 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_17, 0, x_13);
x_18 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_18, 0, x_10);
lean_closure_set(x_18, 1, x_12);
lean_closure_set(x_18, 2, x_16);
lean_closure_set(x_18, 3, x_17);
x_19 = lean_apply_6(x_7, x_14, lean_box(0), lean_box(0), x_9, x_15, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSomeM_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Iter_Total_findSomeM_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Iter_findSome_x3f___redArg___lam__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_5 = lean_box(0);
x_6 = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_6(x_1, x_4, lean_box(0), lean_box(0), x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_apply_6(x_5, x_8, lean_box(0), lean_box(0), x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findSome_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Iter_findSome_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSome_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_5 = lean_box(0);
x_6 = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_6(x_1, x_4, lean_box(0), lean_box(0), x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSome_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_apply_6(x_5, x_8, lean_box(0), lean_box(0), x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findSome_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Iter_Partial_findSome_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSome_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_5 = lean_box(0);
x_6 = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_6(x_1, x_4, lean_box(0), lean_box(0), x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSome_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_10 = lean_box(0);
x_11 = lean_alloc_closure((void*)(l_Std_Iter_findSome_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_apply_6(x_5, x_9, lean_box(0), lean_box(0), x_7, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findSome_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Iter_Total_findSome_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_3);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = l_Std_Iter_findM_x3f___redArg___lam__3(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__3___boxed), 4, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_7);
x_11 = lean_apply_1(x_3, x_7);
lean_inc(x_4);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_11, x_10);
lean_inc(x_4);
x_13 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_12, x_5);
x_14 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_13, x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Iter_findM_x3f___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l_Std_Iter_instForIn_x27___redArg___closed__0;
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_box(0);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_6);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_9);
x_13 = lean_apply_6(x_2, x_8, lean_box(0), lean_box(0), x_3, x_10, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec_ref(x_4);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Std_Iter_instForIn_x27___redArg___closed__0;
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = lean_box(0);
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_11);
x_16 = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(x_16, 0, x_11);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_8);
lean_closure_set(x_16, 3, x_10);
lean_closure_set(x_16, 4, x_15);
lean_closure_set(x_16, 5, x_13);
x_17 = lean_apply_6(x_6, x_12, lean_box(0), lean_box(0), x_7, x_14, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_findM_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Iter_findM_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findM_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l_Std_Iter_instForIn_x27___redArg___closed__0;
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_box(0);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_6);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_9);
x_13 = lean_apply_6(x_2, x_8, lean_box(0), lean_box(0), x_3, x_10, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findM_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec_ref(x_4);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Std_Iter_instForIn_x27___redArg___closed__0;
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = lean_box(0);
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_11);
x_16 = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(x_16, 0, x_11);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_8);
lean_closure_set(x_16, 3, x_10);
lean_closure_set(x_16, 4, x_15);
lean_closure_set(x_16, 5, x_13);
x_17 = lean_apply_6(x_6, x_12, lean_box(0), lean_box(0), x_7, x_14, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_findM_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Iter_Partial_findM_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l_Std_Iter_instForIn_x27___redArg___closed__0;
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_box(0);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_6);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_9);
x_13 = lean_apply_6(x_2, x_8, lean_box(0), lean_box(0), x_3, x_10, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Std_Iter_instForIn_x27___redArg___closed__0;
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_box(0);
lean_inc(x_12);
x_16 = lean_alloc_closure((void*)(l_Std_Iter_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_12);
x_17 = lean_alloc_closure((void*)(l_Std_Iter_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(x_17, 0, x_12);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_9);
lean_closure_set(x_17, 3, x_11);
lean_closure_set(x_17, 4, x_16);
lean_closure_set(x_17, 5, x_14);
x_18 = lean_apply_6(x_6, x_13, lean_box(0), lean_box(0), x_8, x_15, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_findM_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Iter_Total_findM_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_6 = lean_apply_1(x_1, x_3);
x_7 = lean_unbox(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_3);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Iter_find_x3f___redArg___lam__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_5 = lean_box(0);
x_6 = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_6(x_1, x_4, lean_box(0), lean_box(0), x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_8 = lean_box(0);
x_9 = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_apply_6(x_4, x_7, lean_box(0), lean_box(0), x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_find_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Iter_find_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_find_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_5 = lean_box(0);
x_6 = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_6(x_1, x_4, lean_box(0), lean_box(0), x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_8 = lean_box(0);
x_9 = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_apply_6(x_4, x_7, lean_box(0), lean_box(0), x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_find_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Iter_Partial_find_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_find_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_5 = lean_box(0);
x_6 = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_6(x_1, x_4, lean_box(0), lean_box(0), x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Std_Iter_instForIn_x27___redArg___closed__0;
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Std_Iter_find_x3f___redArg___lam__1___boxed), 5, 2);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_apply_6(x_4, x_8, lean_box(0), lean_box(0), x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_find_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Iter_Total_find_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_count___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_count___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_count___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Iter_count___redArg___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Iter_count___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Iter_count___redArg___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Iter_count___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Iter_count___redArg___lam__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_count___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Std_Iter_count___redArg___closed__0;
x_4 = l_Std_Iter_count___redArg___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_apply_6(x_1, x_3, lean_box(0), lean_box(0), x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_count(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Std_Iter_count___redArg___closed__0;
x_7 = l_Std_Iter_count___redArg___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_apply_6(x_4, x_6, lean_box(0), lean_box(0), x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_count___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Iter_count(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_size___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Std_Iter_count___redArg___closed__0;
x_4 = l_Std_Iter_count___redArg___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_apply_6(x_1, x_3, lean_box(0), lean_box(0), x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_size(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Std_Iter_count___redArg___closed__0;
x_7 = l_Std_Iter_count___redArg___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_apply_6(x_4, x_6, lean_box(0), lean_box(0), x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Iter_size(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_count___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Std_Iter_count___redArg___closed__0;
x_4 = l_Std_Iter_count___redArg___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_apply_6(x_1, x_3, lean_box(0), lean_box(0), x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_count(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Std_Iter_count___redArg___closed__0;
x_7 = l_Std_Iter_count___redArg___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_apply_6(x_4, x_6, lean_box(0), lean_box(0), x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_count___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Iter_Partial_count(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_size___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Std_Iter_count___redArg___closed__0;
x_4 = l_Std_Iter_count___redArg___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_apply_6(x_1, x_3, lean_box(0), lean_box(0), x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_size(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Std_Iter_count___redArg___closed__0;
x_7 = l_Std_Iter_count___redArg___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_apply_6(x_4, x_6, lean_box(0), lean_box(0), x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Iter_Partial_size(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Iter_instForIn_x27___redArg___closed__0 = _init_l_Std_Iter_instForIn_x27___redArg___closed__0();
lean_mark_persistent(l_Std_Iter_instForIn_x27___redArg___closed__0);
l_Std_Iter_foldM___redArg___closed__0 = _init_l_Std_Iter_foldM___redArg___closed__0();
lean_mark_persistent(l_Std_Iter_foldM___redArg___closed__0);
l_Std_Iter_count___redArg___closed__0 = _init_l_Std_Iter_count___redArg___closed__0();
lean_mark_persistent(l_Std_Iter_count___redArg___closed__0);
l_Std_Iter_count___redArg___closed__1 = _init_l_Std_Iter_count___redArg___closed__1();
lean_mark_persistent(l_Std_Iter_count___redArg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
