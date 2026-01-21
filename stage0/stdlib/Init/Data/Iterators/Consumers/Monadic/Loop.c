// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Monadic.Loop
// Imports: public import Init.Data.Iterators.Consumers.Monadic.Partial public import Init.Data.Iterators.Internal.LawfulMonadLiftFunction public import Init.WFExtrinsicFix public import Init.Data.Iterators.Consumers.Monadic.Total
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
LEAN_EXPORT lean_object* l_Std_IterM_Total_all___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_any___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_count___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_any___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_drain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_count(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__0(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_allM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_size(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_WithWF_instWellFoundedRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_all___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Std_IterM_foldM___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_allM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg___lam__2(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_IterM_count___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_size___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_count___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_count___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_drain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_anyM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_count___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_WithWF_instWellFoundedRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_IterM_Total_any___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_anyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_WithWF_instWellFoundedRelation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_WithWF_instWellFoundedRelation___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_IteratorLoop_WithWF_instWellFoundedRelation(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_apply_4(x_2, x_3, x_7, lean_box(0), lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0), 4, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_7);
x_10 = lean_apply_3(x_3, x_8, lean_box(0), x_4);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_9);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec_ref(x_6);
x_13 = lean_apply_4(x_2, x_12, x_4, lean_box(0), lean_box(0));
return x_13;
}
default: 
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_apply_2(x_1, lean_box(0), x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__1), 6, 5);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_7);
lean_closure_set(x_10, 4, x_3);
x_11 = lean_apply_1(x_4, x_6);
x_12 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2), 9, 5);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_6);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_1);
lean_closure_set(x_10, 4, x_3);
x_11 = l_WellFounded_opaqueFix_u2083___redArg(x_10, x_4, x_5, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec_ref(x_6);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2), 9, 5);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_14);
lean_closure_set(x_18, 2, x_16);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_7);
x_19 = l_WellFounded_opaqueFix_u2083___redArg(x_18, x_10, x_11, lean_box(0));
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
lean_inc(x_5);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__0), 7, 6);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_9);
lean_closure_set(x_11, 5, x_5);
x_12 = lean_apply_3(x_5, x_10, lean_box(0), x_6);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_1);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec_ref(x_8);
x_15 = l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(x_2, x_3, x_4, x_14, x_6, x_5);
return x_15;
}
default: 
{
lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_16 = lean_apply_2(x_1, lean_box(0), x_6);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_inc(x_3);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__1), 8, 7);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_6);
lean_closure_set(x_10, 5, x_5);
lean_closure_set(x_10, 6, x_8);
x_11 = lean_apply_1(x_1, x_4);
x_12 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(x_2, x_3, x_4, x_5, x_10, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(x_4, x_6, x_7, x_11, x_12, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_3(x_2, x_5, x_6, lean_box(0));
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_2(x_3, x_8, lean_box(0));
return x_9;
}
default: 
{
lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_apply_1(x_4, lean_box(0));
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_3, x_4, lean_box(0));
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_2(x_2, x_6, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0), 4, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_7);
x_10 = lean_apply_3(x_3, x_8, lean_box(0), x_4);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_9);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec_ref(x_6);
x_13 = lean_apply_4(x_2, x_12, x_4, lean_box(0), lean_box(0));
return x_13;
}
default: 
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_apply_2(x_1, lean_box(0), x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__1), 6, 5);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_7);
lean_closure_set(x_10, 4, x_3);
x_11 = lean_apply_1(x_4, x_6);
x_12 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__0), 9, 5);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_8);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_2);
lean_closure_set(x_12, 4, x_3);
x_13 = l_WellFounded_opaqueFix_u2083___redArg(x_12, x_6, x_7, lean_box(0));
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__2), 8, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__2), 8, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_3(x_1, x_4, lean_box(0), x_6);
x_8 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1), 6, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
x_10 = lean_apply_6(x_3, x_4, lean_box(0), lean_box(0), x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2), 8, 4);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_1);
lean_closure_set(x_8, 3, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2), 8, 4);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IteratorLoop_finiteForIn_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
x_8 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1), 6, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
x_10 = lean_apply_6(x_3, x_4, lean_box(0), lean_box(0), x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_10);
x_13 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_6);
lean_closure_set(x_14, 3, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_instForIn_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_7);
x_10 = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(x_10, 0, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_instForInOfIteratorLoop___redArg(x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_instForInOfIteratorLoop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1), 6, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
x_10 = lean_apply_6(x_3, x_4, lean_box(0), lean_box(0), x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_10);
x_13 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_6);
lean_closure_set(x_14, 3, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_Partial_instForIn_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(x_13, 0, x_7);
lean_closure_set(x_13, 1, x_11);
x_14 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_6);
lean_closure_set(x_15, 3, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_IterM_Total_instForIn_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_7);
x_10 = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(x_10, 0, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_Partial_instForInOfIteratorLoop___redArg(x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_Partial_instForInOfIteratorLoop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_7);
x_10 = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(x_10, 0, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___redArg(x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__0), 3, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
x_10 = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__2), 7, 4);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_9);
lean_closure_set(x_10, 3, x_3);
x_11 = lean_apply_6(x_4, x_5, lean_box(0), lean_box(0), x_6, x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_5);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3), 7, 5);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_1);
lean_closure_set(x_9, 4, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_instForMOfIteratorLoop___redArg(x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_instForMOfIteratorLoop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_5);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3), 7, 5);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_2);
lean_closure_set(x_9, 4, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_Partial_instForMOfItreratorLoop___redArg(x_5, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_Partial_instForMOfItreratorLoop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_5);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3), 7, 5);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_1);
lean_closure_set(x_9, 4, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___redArg(x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
static lean_object* _init_l_Std_IterM_foldM___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = l_Std_IterM_foldM___redArg___closed__0;
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_8);
x_13 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_13, 0, x_10);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(x_14, 0, x_9);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_11);
lean_closure_set(x_14, 3, x_8);
lean_closure_set(x_14, 4, x_13);
x_15 = lean_apply_6(x_2, x_12, lean_box(0), lean_box(0), x_6, x_5, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec_ref(x_3);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec_ref(x_13);
x_17 = l_Std_IterM_foldM___redArg___closed__0;
lean_inc(x_14);
x_18 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(x_18, 0, x_9);
lean_closure_set(x_18, 1, x_14);
x_19 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_19, 0, x_16);
x_20 = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(x_20, 0, x_15);
lean_closure_set(x_20, 1, x_10);
lean_closure_set(x_20, 2, x_17);
lean_closure_set(x_20, 3, x_14);
lean_closure_set(x_20, 4, x_19);
x_21 = lean_apply_6(x_8, x_18, lean_box(0), lean_box(0), x_12, x_11, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_IterM_foldM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = l_Std_IterM_foldM___redArg___closed__0;
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_8);
x_13 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_13, 0, x_10);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(x_14, 0, x_9);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_11);
lean_closure_set(x_14, 3, x_8);
lean_closure_set(x_14, 4, x_13);
x_15 = lean_apply_6(x_2, x_12, lean_box(0), lean_box(0), x_6, x_5, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec_ref(x_3);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec_ref(x_13);
x_17 = l_Std_IterM_foldM___redArg___closed__0;
lean_inc(x_14);
x_18 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(x_18, 0, x_9);
lean_closure_set(x_18, 1, x_14);
x_19 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_19, 0, x_16);
x_20 = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(x_20, 0, x_15);
lean_closure_set(x_20, 1, x_10);
lean_closure_set(x_20, 2, x_17);
lean_closure_set(x_20, 3, x_14);
lean_closure_set(x_20, 4, x_19);
x_21 = lean_apply_6(x_8, x_18, lean_box(0), lean_box(0), x_12, x_11, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_IterM_Partial_foldM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = l_Std_IterM_foldM___redArg___closed__0;
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_8);
x_13 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_13, 0, x_10);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(x_14, 0, x_9);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_11);
lean_closure_set(x_14, 3, x_8);
lean_closure_set(x_14, 4, x_13);
x_15 = lean_apply_6(x_2, x_12, lean_box(0), lean_box(0), x_6, x_5, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec_ref(x_3);
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec_ref(x_14);
x_18 = l_Std_IterM_foldM___redArg___closed__0;
lean_inc(x_15);
x_19 = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(x_19, 0, x_9);
lean_closure_set(x_19, 1, x_15);
x_20 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_20, 0, x_17);
x_21 = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_11);
lean_closure_set(x_21, 2, x_18);
lean_closure_set(x_21, 3, x_15);
lean_closure_set(x_21, 4, x_20);
x_22 = lean_apply_6(x_8, x_19, lean_box(0), lean_box(0), x_13, x_12, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_IterM_Total_foldM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_apply_2(x_1, x_7, x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_apply_2(x_2, lean_box(0), x_9);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_9, 0, x_7);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_10, 0, x_8);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_7);
lean_closure_set(x_11, 3, x_10);
x_12 = lean_apply_6(x_2, x_9, lean_box(0), lean_box(0), x_5, x_4, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec_ref(x_5);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_14, 0, x_12);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_15, 0, x_13);
x_16 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(x_16, 0, x_8);
lean_closure_set(x_16, 1, x_13);
lean_closure_set(x_16, 2, x_12);
lean_closure_set(x_16, 3, x_15);
x_17 = lean_apply_6(x_7, x_14, lean_box(0), lean_box(0), x_10, x_9, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_IterM_fold(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_9, 0, x_7);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_10, 0, x_8);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_7);
lean_closure_set(x_11, 3, x_10);
x_12 = lean_apply_6(x_2, x_9, lean_box(0), lean_box(0), x_5, x_4, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec_ref(x_5);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_14, 0, x_12);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_15, 0, x_13);
x_16 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(x_16, 0, x_8);
lean_closure_set(x_16, 1, x_13);
lean_closure_set(x_16, 2, x_12);
lean_closure_set(x_16, 3, x_15);
x_17 = lean_apply_6(x_7, x_14, lean_box(0), lean_box(0), x_10, x_9, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_IterM_Partial_fold(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_9, 0, x_7);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_10, 0, x_8);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_7);
lean_closure_set(x_11, 3, x_10);
x_12 = lean_apply_6(x_2, x_9, lean_box(0), lean_box(0), x_5, x_4, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_dec_ref(x_5);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_15, 0, x_13);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(x_16, 0, x_14);
x_17 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(x_17, 0, x_9);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_13);
lean_closure_set(x_17, 3, x_16);
x_18 = lean_apply_6(x_7, x_15, lean_box(0), lean_box(0), x_11, x_10, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_IterM_Total_fold(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
x_10 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_9, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_IterM_drain___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_box(0);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_5);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_6);
x_10 = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_6);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_apply_6(x_3, x_8, lean_box(0), lean_box(0), x_2, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec_ref(x_3);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_box(0);
lean_inc(x_9);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_12, 0, x_9);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(x_13, 0, x_10);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_10);
lean_closure_set(x_14, 2, x_9);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_apply_6(x_7, x_12, lean_box(0), lean_box(0), x_6, x_11, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_IterM_drain(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_box(0);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_5);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_6);
x_10 = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_6);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_apply_6(x_3, x_8, lean_box(0), lean_box(0), x_2, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec_ref(x_3);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_box(0);
lean_inc(x_9);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_12, 0, x_9);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(x_13, 0, x_10);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_10);
lean_closure_set(x_14, 2, x_9);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_apply_6(x_7, x_12, lean_box(0), lean_box(0), x_6, x_11, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_IterM_Partial_drain(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_box(0);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_5);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_6);
x_10 = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_6);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_apply_6(x_3, x_8, lean_box(0), lean_box(0), x_2, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec_ref(x_3);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_box(0);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_13, 0, x_10);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(x_14, 0, x_11);
x_15 = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_11);
lean_closure_set(x_15, 2, x_10);
lean_closure_set(x_15, 3, x_14);
x_16 = lean_apply_6(x_8, x_13, lean_box(0), lean_box(0), x_7, x_12, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_Total_drain(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__0(uint8_t x_1, lean_object* x_2, uint8_t x_3) {
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
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_3);
x_6 = l_Std_IterM_anyM___redArg___lam__0(x_4, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
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
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
x_9 = l_Std_IterM_anyM___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_7);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_9);
x_14 = lean_box(x_10);
x_15 = lean_apply_6(x_2, x_8, lean_box(0), lean_box(0), x_4, x_14, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_anyM___redArg(x_4, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_anyM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_IterM_anyM___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_anyM___redArg(x_4, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_Partial_anyM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_IterM_anyM___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_IterM_anyM___redArg(x_4, x_6, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_IterM_Total_anyM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_6);
x_8 = l_Std_IterM_anyM___redArg(x_1, x_2, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Std_IterM_anyM___redArg(x_4, x_6, x_11, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_any(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_6);
x_8 = l_Std_IterM_anyM___redArg(x_1, x_2, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Std_IterM_anyM___redArg(x_4, x_6, x_11, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_Partial_any(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_any___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_6);
x_8 = l_Std_IterM_anyM___redArg(x_1, x_2, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_any(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Std_IterM_anyM___redArg(x_4, x_6, x_12, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_any___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_IterM_Total_any(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg___lam__2(lean_object* x_1, uint8_t x_2, uint8_t x_3) {
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
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
x_5 = lean_unbox(x_3);
x_6 = l_Std_IterM_allM___redArg___lam__2(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_allM___redArg___lam__2___boxed), 3, 2);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_9);
x_14 = lean_box(x_10);
x_15 = lean_apply_6(x_2, x_8, lean_box(0), lean_box(0), x_4, x_14, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_allM___redArg(x_4, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_allM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_IterM_allM___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_allM___redArg(x_4, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_Partial_allM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_IterM_allM___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_IterM_allM___redArg(x_4, x_6, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_IterM_Total_allM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_all___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_6);
x_8 = l_Std_IterM_allM___redArg(x_1, x_2, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_all(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Std_IterM_allM___redArg(x_4, x_6, x_11, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_all___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_all(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_6);
x_8 = l_Std_IterM_allM___redArg(x_1, x_2, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Std_IterM_allM___redArg(x_4, x_6, x_11, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_Partial_all(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_all___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_6);
x_8 = l_Std_IterM_allM___redArg(x_1, x_2, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_all(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Std_IterM_allM___redArg(x_4, x_6, x_12, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_all___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_IterM_Total_all(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_IterM_findSomeM_x3f___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_9);
x_13 = lean_apply_6(x_2, x_8, lean_box(0), lean_box(0), x_3, x_10, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_13, 0, x_11);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_12);
x_17 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_17, 0, x_9);
lean_closure_set(x_17, 1, x_11);
lean_closure_set(x_17, 2, x_16);
lean_closure_set(x_17, 3, x_14);
x_18 = lean_apply_6(x_7, x_13, lean_box(0), lean_box(0), x_8, x_15, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_IterM_findSomeM_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_9);
x_13 = lean_apply_6(x_2, x_8, lean_box(0), lean_box(0), x_3, x_10, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_13, 0, x_11);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_12);
x_17 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_17, 0, x_9);
lean_closure_set(x_17, 1, x_11);
lean_closure_set(x_17, 2, x_16);
lean_closure_set(x_17, 3, x_14);
x_18 = lean_apply_6(x_7, x_13, lean_box(0), lean_box(0), x_8, x_15, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_IterM_Partial_findSomeM_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_9);
x_13 = lean_apply_6(x_2, x_8, lean_box(0), lean_box(0), x_3, x_10, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_14, 0, x_12);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_15, 0, x_13);
x_16 = lean_box(0);
x_17 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_13);
x_18 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(x_18, 0, x_10);
lean_closure_set(x_18, 1, x_12);
lean_closure_set(x_18, 2, x_17);
lean_closure_set(x_18, 3, x_15);
x_19 = lean_apply_6(x_7, x_14, lean_box(0), lean_box(0), x_9, x_16, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_IterM_Total_findSomeM_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_apply_1(x_1, x_6);
x_10 = lean_apply_2(x_2, lean_box(0), x_9);
lean_inc(x_3);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_4);
x_12 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_11, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_findSome_x3f___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_box(0);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_6);
lean_closure_set(x_12, 3, x_11);
lean_closure_set(x_12, 4, x_9);
x_13 = lean_apply_6(x_2, x_8, lean_box(0), lean_box(0), x_3, x_10, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_13, 0, x_11);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_box(0);
lean_inc(x_12);
x_16 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_12);
x_17 = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(x_17, 0, x_9);
lean_closure_set(x_17, 1, x_12);
lean_closure_set(x_17, 2, x_11);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_14);
x_18 = lean_apply_6(x_7, x_13, lean_box(0), lean_box(0), x_8, x_15, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_IterM_findSome_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_box(0);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_6);
lean_closure_set(x_12, 3, x_11);
lean_closure_set(x_12, 4, x_9);
x_13 = lean_apply_6(x_2, x_8, lean_box(0), lean_box(0), x_3, x_10, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_13, 0, x_11);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_box(0);
lean_inc(x_12);
x_16 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_12);
x_17 = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(x_17, 0, x_9);
lean_closure_set(x_17, 1, x_12);
lean_closure_set(x_17, 2, x_11);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_14);
x_18 = lean_apply_6(x_7, x_13, lean_box(0), lean_box(0), x_8, x_15, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_IterM_Partial_findSome_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_box(0);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_6);
lean_closure_set(x_12, 3, x_11);
lean_closure_set(x_12, 4, x_9);
x_13 = lean_apply_6(x_2, x_8, lean_box(0), lean_box(0), x_3, x_10, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_14, 0, x_12);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_15, 0, x_13);
x_16 = lean_box(0);
lean_inc(x_13);
x_17 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_13);
x_18 = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(x_18, 0, x_10);
lean_closure_set(x_18, 1, x_13);
lean_closure_set(x_18, 2, x_12);
lean_closure_set(x_18, 3, x_17);
lean_closure_set(x_18, 4, x_15);
x_19 = lean_apply_6(x_7, x_14, lean_box(0), lean_box(0), x_9, x_16, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_IterM_Total_findSome_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
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
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = l_Std_IterM_findM_x3f___redArg___lam__3(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__3___boxed), 4, 3);
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
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_IterM_findM_x3f___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_box(0);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
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
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_12, 0, x_10);
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = lean_box(0);
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_11);
x_16 = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
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
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_findM_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_box(0);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
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
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_12, 0, x_10);
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = lean_box(0);
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_11);
x_16 = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
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
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_Partial_findM_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_box(0);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
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
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_13, 0, x_11);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_box(0);
lean_inc(x_12);
x_16 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_12);
x_17 = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
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
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_IterM_Total_findM_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_7);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__3___boxed), 4, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_7);
x_11 = lean_apply_1(x_3, x_7);
x_12 = lean_apply_2(x_1, lean_box(0), x_11);
lean_inc(x_4);
x_13 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_12, x_10);
lean_inc(x_4);
x_14 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_13, x_5);
x_15 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_14, x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_IterM_find_x3f___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_box(0);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
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
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_12, 0, x_10);
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = lean_box(0);
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_11);
x_16 = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
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
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_find_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_box(0);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
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
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_12, 0, x_10);
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = lean_box(0);
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_11);
x_16 = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
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
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_IterM_Partial_find_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_6);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_box(0);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
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
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_13, 0, x_11);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_box(0);
lean_inc(x_12);
x_16 = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_12);
x_17 = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
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
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_IterM_Total_find_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_count___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_count___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_6, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_apply_2(x_1, lean_box(0), x_9);
x_11 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_10, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_count___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_IterM_count___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_count___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_5);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_count___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_6);
x_10 = lean_alloc_closure((void*)(l_Std_IterM_count___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_9);
x_11 = lean_apply_6(x_1, x_8, lean_box(0), lean_box(0), x_3, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_count(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_12, 0, x_9);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_count___redArg___lam__1), 2, 1);
lean_closure_set(x_13, 0, x_10);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_count___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_9);
lean_closure_set(x_14, 2, x_13);
x_15 = lean_apply_6(x_5, x_12, lean_box(0), lean_box(0), x_7, x_11, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_count___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_IterM_count(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_size___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_5);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_count___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_6);
x_10 = lean_alloc_closure((void*)(l_Std_IterM_count___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_9);
x_11 = lean_apply_6(x_1, x_8, lean_box(0), lean_box(0), x_3, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_size(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_12, 0, x_9);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_count___redArg___lam__1), 2, 1);
lean_closure_set(x_13, 0, x_10);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_count___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_9);
lean_closure_set(x_14, 2, x_13);
x_15 = lean_apply_6(x_5, x_12, lean_box(0), lean_box(0), x_7, x_11, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_IterM_size(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_5);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_count___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_6);
x_10 = lean_alloc_closure((void*)(l_Std_IterM_count___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_9);
x_11 = lean_apply_6(x_1, x_8, lean_box(0), lean_box(0), x_3, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_12, 0, x_9);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_count___redArg___lam__1), 2, 1);
lean_closure_set(x_13, 0, x_10);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_count___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_9);
lean_closure_set(x_14, 2, x_13);
x_15 = lean_apply_6(x_5, x_12, lean_box(0), lean_box(0), x_7, x_11, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_IterM_Partial_count(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_8, 0, x_5);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Std_IterM_count___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_6);
x_10 = lean_alloc_closure((void*)(l_Std_IterM_count___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_9);
x_11 = lean_apply_6(x_1, x_8, lean_box(0), lean_box(0), x_3, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
x_12 = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(x_12, 0, x_9);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Std_IterM_count___redArg___lam__1), 2, 1);
lean_closure_set(x_13, 0, x_10);
x_14 = lean_alloc_closure((void*)(l_Std_IterM_count___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_9);
lean_closure_set(x_14, 2, x_13);
x_15 = lean_apply_6(x_5, x_12, lean_box(0), lean_box(0), x_7, x_11, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_IterM_Partial_size(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Partial(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(uint8_t builtin);
lean_object* initialize_Init_WFExtrinsicFix(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Total(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Monadic_Partial(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFExtrinsicFix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_IterM_foldM___redArg___closed__0 = _init_l_Std_IterM_foldM___redArg___closed__0();
lean_mark_persistent(l_Std_IterM_foldM___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
