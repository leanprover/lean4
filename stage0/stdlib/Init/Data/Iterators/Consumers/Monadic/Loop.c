// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Monadic.Loop
// Imports: public import Init.Data.Iterators.Consumers.Monadic.Partial public import Init.Data.Iterators.Internal.LawfulMonadLiftFunction public import Init.WFExtrinsicFix public import Init.Data.Iterators.Consumers.Monadic.Total import Init.PropLemmas
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_WithWF_instWellFoundedRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_WithWF_instWellFoundedRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_IterM_foldM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_IterM_foldM___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_IterM_foldM___redArg___closed__0 = (const lean_object*)&l_Std_IterM_foldM___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_drain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_drain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__0(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_anyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_anyM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_any___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_any___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_any___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg___lam__2(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_allM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_allM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_all___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_all___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_first_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_first_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_first_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_IterM_isEmpty___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_IterM_isEmpty___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_IterM_isEmpty___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_isEmpty___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Total_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_length(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_length___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_count___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_count(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_count___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_size___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_size(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IteratorLoop_WithWF_instWellFoundedRelation(lean_object* v_00_u03b1_1_, lean_object* v_m_2_, lean_object* v_00_u03b2_3_, lean_object* v_inst_4_, lean_object* v_00_u03b3_5_, lean_object* v_PlausibleForInStep_6_, lean_object* v_hwf_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_WithWF_instWellFoundedRelation___boxed(lean_object* v_00_u03b1_9_, lean_object* v_m_10_, lean_object* v_00_u03b2_11_, lean_object* v_inst_12_, lean_object* v_00_u03b3_13_, lean_object* v_PlausibleForInStep_14_, lean_object* v_hwf_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Std_IteratorLoop_WithWF_instWellFoundedRelation(v_00_u03b1_9_, v_m_10_, v_00_u03b2_11_, v_inst_12_, v_00_u03b3_13_, v_PlausibleForInStep_14_, v_hwf_15_);
lean_dec(v_inst_12_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0(lean_object* v_toPure_17_, lean_object* v_recur_18_, lean_object* v_it_19_, lean_object* v_____do__lift_20_){
_start:
{
if (lean_obj_tag(v_____do__lift_20_) == 0)
{
lean_object* v_a_21_; lean_object* v___x_22_; 
lean_dec(v_it_19_);
lean_dec(v_recur_18_);
v_a_21_ = lean_ctor_get(v_____do__lift_20_, 0);
lean_inc(v_a_21_);
lean_dec_ref(v_____do__lift_20_);
v___x_22_ = lean_apply_2(v_toPure_17_, lean_box(0), v_a_21_);
return v___x_22_;
}
else
{
lean_object* v_a_23_; lean_object* v___x_24_; 
lean_dec(v_toPure_17_);
v_a_23_ = lean_ctor_get(v_____do__lift_20_, 0);
lean_inc(v_a_23_);
lean_dec_ref(v_____do__lift_20_);
v___x_24_ = lean_apply_4(v_recur_18_, v_it_19_, v_a_23_, lean_box(0), lean_box(0));
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__1(lean_object* v_toPure_25_, lean_object* v_recur_26_, lean_object* v_f_27_, lean_object* v_acc_28_, lean_object* v_toBind_29_, lean_object* v_s_30_){
_start:
{
switch(lean_obj_tag(v_s_30_))
{
case 0:
{
lean_object* v_it_31_; lean_object* v_out_32_; lean_object* v___f_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v_it_31_ = lean_ctor_get(v_s_30_, 0);
lean_inc(v_it_31_);
v_out_32_ = lean_ctor_get(v_s_30_, 1);
lean_inc(v_out_32_);
lean_dec_ref(v_s_30_);
v___f_33_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_33_, 0, v_toPure_25_);
lean_closure_set(v___f_33_, 1, v_recur_26_);
lean_closure_set(v___f_33_, 2, v_it_31_);
v___x_34_ = lean_apply_3(v_f_27_, v_out_32_, lean_box(0), v_acc_28_);
v___x_35_ = lean_apply_4(v_toBind_29_, lean_box(0), lean_box(0), v___x_34_, v___f_33_);
return v___x_35_;
}
case 1:
{
lean_object* v_it_36_; lean_object* v___x_37_; 
lean_dec(v_toBind_29_);
lean_dec(v_f_27_);
lean_dec(v_toPure_25_);
v_it_36_ = lean_ctor_get(v_s_30_, 0);
lean_inc(v_it_36_);
lean_dec_ref(v_s_30_);
v___x_37_ = lean_apply_4(v_recur_26_, v_it_36_, v_acc_28_, lean_box(0), lean_box(0));
return v___x_37_;
}
default: 
{
lean_object* v___x_38_; 
lean_dec(v_toBind_29_);
lean_dec(v_f_27_);
lean_dec(v_recur_26_);
v___x_38_ = lean_apply_2(v_toPure_25_, lean_box(0), v_acc_28_);
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2(lean_object* v_toPure_39_, lean_object* v_f_40_, lean_object* v_toBind_41_, lean_object* v_inst_42_, lean_object* v_lift_43_, lean_object* v_it_44_, lean_object* v_acc_45_, lean_object* v_hP_46_, lean_object* v_recur_47_){
_start:
{
lean_object* v___f_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___f_48_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__1), 6, 5);
lean_closure_set(v___f_48_, 0, v_toPure_39_);
lean_closure_set(v___f_48_, 1, v_recur_47_);
lean_closure_set(v___f_48_, 2, v_f_40_);
lean_closure_set(v___f_48_, 3, v_acc_45_);
lean_closure_set(v___f_48_, 4, v_toBind_41_);
v___x_49_ = lean_apply_1(v_inst_42_, v_it_44_);
v___x_50_ = lean_apply_4(v_lift_43_, lean_box(0), lean_box(0), v___f_48_, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg(lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_lift_53_, lean_object* v_it_54_, lean_object* v_init_55_, lean_object* v_f_56_){
_start:
{
lean_object* v_toApplicative_57_; lean_object* v_toBind_58_; lean_object* v_toPure_59_; lean_object* v___f_60_; lean_object* v___x_61_; 
v_toApplicative_57_ = lean_ctor_get(v_inst_52_, 0);
lean_inc_ref(v_toApplicative_57_);
v_toBind_58_ = lean_ctor_get(v_inst_52_, 1);
lean_inc(v_toBind_58_);
lean_dec_ref(v_inst_52_);
v_toPure_59_ = lean_ctor_get(v_toApplicative_57_, 1);
lean_inc(v_toPure_59_);
lean_dec_ref(v_toApplicative_57_);
v___f_60_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2), 9, 5);
lean_closure_set(v___f_60_, 0, v_toPure_59_);
lean_closure_set(v___f_60_, 1, v_f_56_);
lean_closure_set(v___f_60_, 2, v_toBind_58_);
lean_closure_set(v___f_60_, 3, v_inst_51_);
lean_closure_set(v___f_60_, 4, v_lift_53_);
v___x_61_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_60_, v_it_54_, v_init_55_, lean_box(0));
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27(lean_object* v_m_62_, lean_object* v_00_u03b1_63_, lean_object* v_00_u03b2_64_, lean_object* v_inst_65_, lean_object* v_n_66_, lean_object* v_inst_67_, lean_object* v_lift_68_, lean_object* v_00_u03b3_69_, lean_object* v_PlausibleForInStep_70_, lean_object* v_it_71_, lean_object* v_init_72_, lean_object* v_P_73_, lean_object* v_hP_74_, lean_object* v_f_75_){
_start:
{
lean_object* v_toApplicative_76_; lean_object* v_toBind_77_; lean_object* v_toPure_78_; lean_object* v___f_79_; lean_object* v___x_80_; 
v_toApplicative_76_ = lean_ctor_get(v_inst_67_, 0);
lean_inc_ref(v_toApplicative_76_);
v_toBind_77_ = lean_ctor_get(v_inst_67_, 1);
lean_inc(v_toBind_77_);
lean_dec_ref(v_inst_67_);
v_toPure_78_ = lean_ctor_get(v_toApplicative_76_, 1);
lean_inc(v_toPure_78_);
lean_dec_ref(v_toApplicative_76_);
v___f_79_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2), 9, 5);
lean_closure_set(v___f_79_, 0, v_toPure_78_);
lean_closure_set(v___f_79_, 1, v_f_75_);
lean_closure_set(v___f_79_, 2, v_toBind_77_);
lean_closure_set(v___f_79_, 3, v_inst_65_);
lean_closure_set(v___f_79_, 4, v_lift_68_);
v___x_80_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_79_, v_it_71_, v_init_72_, lean_box(0));
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__1(lean_object* v_toPure_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_lift_84_, lean_object* v_f_85_, lean_object* v_init_86_, lean_object* v_toBind_87_, lean_object* v_s_88_){
_start:
{
switch(lean_obj_tag(v_s_88_))
{
case 0:
{
lean_object* v_it_89_; lean_object* v_out_90_; lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_it_89_ = lean_ctor_get(v_s_88_, 0);
lean_inc(v_it_89_);
v_out_90_ = lean_ctor_get(v_s_88_, 1);
lean_inc(v_out_90_);
lean_dec_ref(v_s_88_);
lean_inc(v_f_85_);
v___f_91_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__0), 7, 6);
lean_closure_set(v___f_91_, 0, v_toPure_81_);
lean_closure_set(v___f_91_, 1, v_inst_82_);
lean_closure_set(v___f_91_, 2, v_inst_83_);
lean_closure_set(v___f_91_, 3, v_lift_84_);
lean_closure_set(v___f_91_, 4, v_it_89_);
lean_closure_set(v___f_91_, 5, v_f_85_);
v___x_92_ = lean_apply_3(v_f_85_, v_out_90_, lean_box(0), v_init_86_);
v___x_93_ = lean_apply_4(v_toBind_87_, lean_box(0), lean_box(0), v___x_92_, v___f_91_);
return v___x_93_;
}
case 1:
{
lean_object* v_it_94_; lean_object* v___x_95_; 
lean_dec(v_toBind_87_);
lean_dec(v_toPure_81_);
v_it_94_ = lean_ctor_get(v_s_88_, 0);
lean_inc(v_it_94_);
lean_dec_ref(v_s_88_);
v___x_95_ = l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(v_inst_82_, v_inst_83_, v_lift_84_, v_it_94_, v_init_86_, v_f_85_);
return v___x_95_;
}
default: 
{
lean_object* v___x_96_; 
lean_dec(v_toBind_87_);
lean_dec(v_f_85_);
lean_dec(v_lift_84_);
lean_dec_ref(v_inst_83_);
lean_dec(v_inst_82_);
v___x_96_ = lean_apply_2(v_toPure_81_, lean_box(0), v_init_86_);
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_lift_99_, lean_object* v_it_100_, lean_object* v_init_101_, lean_object* v_f_102_){
_start:
{
lean_object* v_toApplicative_103_; lean_object* v_toBind_104_; lean_object* v_toPure_105_; lean_object* v___f_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_toApplicative_103_ = lean_ctor_get(v_inst_98_, 0);
v_toBind_104_ = lean_ctor_get(v_inst_98_, 1);
lean_inc(v_toBind_104_);
v_toPure_105_ = lean_ctor_get(v_toApplicative_103_, 1);
lean_inc(v_toPure_105_);
lean_inc(v_lift_99_);
lean_inc(v_inst_97_);
v___f_106_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__1), 8, 7);
lean_closure_set(v___f_106_, 0, v_toPure_105_);
lean_closure_set(v___f_106_, 1, v_inst_97_);
lean_closure_set(v___f_106_, 2, v_inst_98_);
lean_closure_set(v___f_106_, 3, v_lift_99_);
lean_closure_set(v___f_106_, 4, v_f_102_);
lean_closure_set(v___f_106_, 5, v_init_101_);
lean_closure_set(v___f_106_, 6, v_toBind_104_);
v___x_107_ = lean_apply_1(v_inst_97_, v_it_100_);
v___x_108_ = lean_apply_4(v_lift_99_, lean_box(0), lean_box(0), v___f_106_, v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__0(lean_object* v_toPure_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_lift_112_, lean_object* v_it_113_, lean_object* v_f_114_, lean_object* v_____do__lift_115_){
_start:
{
if (lean_obj_tag(v_____do__lift_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_117_; 
lean_dec(v_f_114_);
lean_dec(v_it_113_);
lean_dec(v_lift_112_);
lean_dec_ref(v_inst_111_);
lean_dec(v_inst_110_);
v_a_116_ = lean_ctor_get(v_____do__lift_115_, 0);
lean_inc(v_a_116_);
lean_dec_ref(v_____do__lift_115_);
v___x_117_ = lean_apply_2(v_toPure_109_, lean_box(0), v_a_116_);
return v___x_117_;
}
else
{
lean_object* v_a_118_; lean_object* v___x_119_; 
lean_dec(v_toPure_109_);
v_a_118_ = lean_ctor_get(v_____do__lift_115_, 0);
lean_inc(v_a_118_);
lean_dec_ref(v_____do__lift_115_);
v___x_119_ = l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(v_inst_110_, v_inst_111_, v_lift_112_, v_it_113_, v_a_118_, v_f_114_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf(lean_object* v_m_120_, lean_object* v_00_u03b1_121_, lean_object* v_00_u03b2_122_, lean_object* v_inst_123_, lean_object* v_n_124_, lean_object* v_inst_125_, lean_object* v_lift_126_, lean_object* v_00_u03b3_127_, lean_object* v_PlausibleForInStep_128_, lean_object* v_wf_129_, lean_object* v_it_130_, lean_object* v_init_131_, lean_object* v_P_132_, lean_object* v_hP_133_, lean_object* v_f_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(v_inst_123_, v_inst_125_, v_lift_126_, v_it_130_, v_init_131_, v_f_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(lean_object* v_x_136_, lean_object* v_h__1_137_, lean_object* v_h__2_138_, lean_object* v_h__3_139_){
_start:
{
switch(lean_obj_tag(v_x_136_))
{
case 0:
{
lean_object* v_it_140_; lean_object* v_out_141_; lean_object* v___x_142_; 
lean_dec(v_h__3_139_);
lean_dec(v_h__2_138_);
v_it_140_ = lean_ctor_get(v_x_136_, 0);
lean_inc(v_it_140_);
v_out_141_ = lean_ctor_get(v_x_136_, 1);
lean_inc(v_out_141_);
lean_dec_ref(v_x_136_);
v___x_142_ = lean_apply_3(v_h__1_137_, v_it_140_, v_out_141_, lean_box(0));
return v___x_142_;
}
case 1:
{
lean_object* v_it_143_; lean_object* v___x_144_; 
lean_dec(v_h__3_139_);
lean_dec(v_h__1_137_);
v_it_143_ = lean_ctor_get(v_x_136_, 0);
lean_inc(v_it_143_);
lean_dec_ref(v_x_136_);
v___x_144_ = lean_apply_2(v_h__2_138_, v_it_143_, lean_box(0));
return v___x_144_;
}
default: 
{
lean_object* v___x_145_; 
lean_dec(v_h__2_138_);
lean_dec(v_h__1_137_);
v___x_145_ = lean_apply_1(v_h__3_139_, lean_box(0));
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(lean_object* v_m_146_, lean_object* v_00_u03b1_147_, lean_object* v_00_u03b2_148_, lean_object* v_inst_149_, lean_object* v_it_150_, lean_object* v_motive_151_, lean_object* v_x_152_, lean_object* v_h__1_153_, lean_object* v_h__2_154_, lean_object* v_h__3_155_){
_start:
{
switch(lean_obj_tag(v_x_152_))
{
case 0:
{
lean_object* v_it_156_; lean_object* v_out_157_; lean_object* v___x_158_; 
lean_dec(v_h__3_155_);
lean_dec(v_h__2_154_);
v_it_156_ = lean_ctor_get(v_x_152_, 0);
lean_inc(v_it_156_);
v_out_157_ = lean_ctor_get(v_x_152_, 1);
lean_inc(v_out_157_);
lean_dec_ref(v_x_152_);
v___x_158_ = lean_apply_3(v_h__1_153_, v_it_156_, v_out_157_, lean_box(0));
return v___x_158_;
}
case 1:
{
lean_object* v_it_159_; lean_object* v___x_160_; 
lean_dec(v_h__3_155_);
lean_dec(v_h__1_153_);
v_it_159_ = lean_ctor_get(v_x_152_, 0);
lean_inc(v_it_159_);
lean_dec_ref(v_x_152_);
v___x_160_ = lean_apply_2(v_h__2_154_, v_it_159_, lean_box(0));
return v___x_160_;
}
default: 
{
lean_object* v___x_161_; 
lean_dec(v_h__2_154_);
lean_dec(v_h__1_153_);
v___x_161_ = lean_apply_1(v_h__3_155_, lean_box(0));
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(lean_object* v_m_162_, lean_object* v_00_u03b1_163_, lean_object* v_00_u03b2_164_, lean_object* v_inst_165_, lean_object* v_it_166_, lean_object* v_motive_167_, lean_object* v_x_168_, lean_object* v_h__1_169_, lean_object* v_h__2_170_, lean_object* v_h__3_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(v_m_162_, v_00_u03b1_163_, v_00_u03b2_164_, v_inst_165_, v_it_166_, v_motive_167_, v_x_168_, v_h__1_169_, v_h__2_170_, v_h__3_171_);
lean_dec(v_it_166_);
lean_dec(v_inst_165_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(lean_object* v_____do__lift_173_, lean_object* v_h__1_174_, lean_object* v_h__2_175_){
_start:
{
if (lean_obj_tag(v_____do__lift_173_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_177_; 
lean_dec(v_h__1_174_);
v_a_176_ = lean_ctor_get(v_____do__lift_173_, 0);
lean_inc(v_a_176_);
lean_dec_ref(v_____do__lift_173_);
v___x_177_ = lean_apply_2(v_h__2_175_, v_a_176_, lean_box(0));
return v___x_177_;
}
else
{
lean_object* v_a_178_; lean_object* v___x_179_; 
lean_dec(v_h__2_175_);
v_a_178_ = lean_ctor_get(v_____do__lift_173_, 0);
lean_inc(v_a_178_);
lean_dec_ref(v_____do__lift_173_);
v___x_179_ = lean_apply_2(v_h__1_174_, v_a_178_, lean_box(0));
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(lean_object* v_00_u03b2_180_, lean_object* v_00_u03b3_181_, lean_object* v_PlausibleForInStep_182_, lean_object* v_acc_183_, lean_object* v_out_184_, lean_object* v_motive_185_, lean_object* v_____do__lift_186_, lean_object* v_h__1_187_, lean_object* v_h__2_188_){
_start:
{
if (lean_obj_tag(v_____do__lift_186_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_190_; 
lean_dec(v_h__1_187_);
v_a_189_ = lean_ctor_get(v_____do__lift_186_, 0);
lean_inc(v_a_189_);
lean_dec_ref(v_____do__lift_186_);
v___x_190_ = lean_apply_2(v_h__2_188_, v_a_189_, lean_box(0));
return v___x_190_;
}
else
{
lean_object* v_a_191_; lean_object* v___x_192_; 
lean_dec(v_h__2_188_);
v_a_191_ = lean_ctor_get(v_____do__lift_186_, 0);
lean_inc(v_a_191_);
lean_dec_ref(v_____do__lift_186_);
v___x_192_ = lean_apply_2(v_h__1_187_, v_a_191_, lean_box(0));
return v___x_192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(lean_object* v_00_u03b2_193_, lean_object* v_00_u03b3_194_, lean_object* v_PlausibleForInStep_195_, lean_object* v_acc_196_, lean_object* v_out_197_, lean_object* v_motive_198_, lean_object* v_____do__lift_199_, lean_object* v_h__1_200_, lean_object* v_h__2_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(v_00_u03b2_193_, v_00_u03b3_194_, v_PlausibleForInStep_195_, v_acc_196_, v_out_197_, v_motive_198_, v_____do__lift_199_, v_h__1_200_, v_h__2_201_);
lean_dec(v_out_197_);
lean_dec(v_acc_196_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__1(lean_object* v_toPure_203_, lean_object* v_recur_204_, lean_object* v___y_205_, lean_object* v_acc_206_, lean_object* v_toBind_207_, lean_object* v_s_208_){
_start:
{
switch(lean_obj_tag(v_s_208_))
{
case 0:
{
lean_object* v_it_209_; lean_object* v_out_210_; lean_object* v___f_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_it_209_ = lean_ctor_get(v_s_208_, 0);
lean_inc(v_it_209_);
v_out_210_ = lean_ctor_get(v_s_208_, 1);
lean_inc(v_out_210_);
lean_dec_ref(v_s_208_);
v___f_211_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_211_, 0, v_toPure_203_);
lean_closure_set(v___f_211_, 1, v_recur_204_);
lean_closure_set(v___f_211_, 2, v_it_209_);
v___x_212_ = lean_apply_3(v___y_205_, v_out_210_, lean_box(0), v_acc_206_);
v___x_213_ = lean_apply_4(v_toBind_207_, lean_box(0), lean_box(0), v___x_212_, v___f_211_);
return v___x_213_;
}
case 1:
{
lean_object* v_it_214_; lean_object* v___x_215_; 
lean_dec(v_toBind_207_);
lean_dec(v___y_205_);
lean_dec(v_toPure_203_);
v_it_214_ = lean_ctor_get(v_s_208_, 0);
lean_inc(v_it_214_);
lean_dec_ref(v_s_208_);
v___x_215_ = lean_apply_4(v_recur_204_, v_it_214_, v_acc_206_, lean_box(0), lean_box(0));
return v___x_215_;
}
default: 
{
lean_object* v___x_216_; 
lean_dec(v_toBind_207_);
lean_dec(v___y_205_);
lean_dec(v_recur_204_);
v___x_216_ = lean_apply_2(v_toPure_203_, lean_box(0), v_acc_206_);
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__0(lean_object* v_toPure_217_, lean_object* v___y_218_, lean_object* v_toBind_219_, lean_object* v_inst_220_, lean_object* v_lift_221_, lean_object* v_it_222_, lean_object* v_acc_223_, lean_object* v_hP_224_, lean_object* v_recur_225_){
_start:
{
lean_object* v___f_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___f_226_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__1), 6, 5);
lean_closure_set(v___f_226_, 0, v_toPure_217_);
lean_closure_set(v___f_226_, 1, v_recur_225_);
lean_closure_set(v___f_226_, 2, v___y_218_);
lean_closure_set(v___f_226_, 3, v_acc_223_);
lean_closure_set(v___f_226_, 4, v_toBind_219_);
v___x_227_ = lean_apply_1(v_inst_220_, v_it_222_);
v___x_228_ = lean_apply_4(v_lift_221_, lean_box(0), lean_box(0), v___f_226_, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__2(lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v_lift_231_, lean_object* v_00_u03b3_232_, lean_object* v_Pl_233_, lean_object* v_it_234_, lean_object* v_init_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_toApplicative_237_; lean_object* v_toBind_238_; lean_object* v_toPure_239_; lean_object* v___f_240_; lean_object* v___x_241_; 
v_toApplicative_237_ = lean_ctor_get(v_inst_229_, 0);
lean_inc_ref(v_toApplicative_237_);
v_toBind_238_ = lean_ctor_get(v_inst_229_, 1);
lean_inc(v_toBind_238_);
lean_dec_ref(v_inst_229_);
v_toPure_239_ = lean_ctor_get(v_toApplicative_237_, 1);
lean_inc(v_toPure_239_);
lean_dec_ref(v_toApplicative_237_);
v___f_240_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__0), 9, 5);
lean_closure_set(v___f_240_, 0, v_toPure_239_);
lean_closure_set(v___f_240_, 1, v___y_236_);
lean_closure_set(v___f_240_, 2, v_toBind_238_);
lean_closure_set(v___f_240_, 3, v_inst_230_);
lean_closure_set(v___f_240_, 4, v_lift_231_);
v___x_241_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_240_, v_it_234_, v_init_235_, lean_box(0));
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg(lean_object* v_inst_242_, lean_object* v_inst_243_){
_start:
{
lean_object* v___f_244_; 
v___f_244_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__2), 8, 2);
lean_closure_set(v___f_244_, 0, v_inst_242_);
lean_closure_set(v___f_244_, 1, v_inst_243_);
return v___f_244_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation(lean_object* v_00_u03b2_245_, lean_object* v_00_u03b1_246_, lean_object* v_m_247_, lean_object* v_n_248_, lean_object* v_inst_249_, lean_object* v_inst_250_){
_start:
{
lean_object* v___f_251_; 
v___f_251_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__2), 8, 2);
lean_closure_set(v___f_251_, 0, v_inst_249_);
lean_closure_set(v___f_251_, 1, v_inst_250_);
return v___f_251_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0(lean_object* v_toPure_252_, lean_object* v_____do__lift_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_apply_2(v_toPure_252_, lean_box(0), v_____do__lift_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1(lean_object* v_f_255_, lean_object* v_toBind_256_, lean_object* v___f_257_, lean_object* v_x1_258_, lean_object* v_x2_259_, lean_object* v_x3_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_apply_3(v_f_255_, v_x1_258_, lean_box(0), v_x3_260_);
v___x_262_ = lean_apply_4(v_toBind_256_, lean_box(0), lean_box(0), v___x_261_, v___f_257_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2(lean_object* v_toBind_263_, lean_object* v___f_264_, lean_object* v_inst_265_, lean_object* v_lift_266_, lean_object* v_00_u03b3_267_, lean_object* v_it_268_, lean_object* v_init_269_, lean_object* v_f_270_){
_start:
{
lean_object* v___f_271_; lean_object* v___x_272_; 
v___f_271_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1), 6, 3);
lean_closure_set(v___f_271_, 0, v_f_270_);
lean_closure_set(v___f_271_, 1, v_toBind_263_);
lean_closure_set(v___f_271_, 2, v___f_264_);
v___x_272_ = lean_apply_6(v_inst_265_, v_lift_266_, lean_box(0), lean_box(0), v_it_268_, v_init_269_, v___f_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg(lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_lift_275_){
_start:
{
lean_object* v_toApplicative_276_; lean_object* v_toBind_277_; lean_object* v_toPure_278_; lean_object* v___f_279_; lean_object* v___f_280_; 
v_toApplicative_276_ = lean_ctor_get(v_inst_274_, 0);
lean_inc_ref(v_toApplicative_276_);
v_toBind_277_ = lean_ctor_get(v_inst_274_, 1);
lean_inc(v_toBind_277_);
lean_dec_ref(v_inst_274_);
v_toPure_278_ = lean_ctor_get(v_toApplicative_276_, 1);
lean_inc(v_toPure_278_);
lean_dec_ref(v_toApplicative_276_);
v___f_279_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_279_, 0, v_toPure_278_);
v___f_280_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2), 8, 4);
lean_closure_set(v___f_280_, 0, v_toBind_277_);
lean_closure_set(v___f_280_, 1, v___f_279_);
lean_closure_set(v___f_280_, 2, v_inst_273_);
lean_closure_set(v___f_280_, 3, v_lift_275_);
return v___f_280_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27(lean_object* v_m_281_, lean_object* v_n_282_, lean_object* v_00_u03b1_283_, lean_object* v_00_u03b2_284_, lean_object* v_inst_285_, lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v_lift_288_){
_start:
{
lean_object* v_toApplicative_289_; lean_object* v_toBind_290_; lean_object* v_toPure_291_; lean_object* v___f_292_; lean_object* v___f_293_; 
v_toApplicative_289_ = lean_ctor_get(v_inst_287_, 0);
lean_inc_ref(v_toApplicative_289_);
v_toBind_290_ = lean_ctor_get(v_inst_287_, 1);
lean_inc(v_toBind_290_);
lean_dec_ref(v_inst_287_);
v_toPure_291_ = lean_ctor_get(v_toApplicative_289_, 1);
lean_inc(v_toPure_291_);
lean_dec_ref(v_toApplicative_289_);
v___f_292_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_292_, 0, v_toPure_291_);
v___f_293_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2), 8, 4);
lean_closure_set(v___f_293_, 0, v_toBind_290_);
lean_closure_set(v___f_293_, 1, v___f_292_);
lean_closure_set(v___f_293_, 2, v_inst_286_);
lean_closure_set(v___f_293_, 3, v_lift_288_);
return v___f_293_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___boxed(lean_object* v_m_294_, lean_object* v_n_295_, lean_object* v_00_u03b1_296_, lean_object* v_00_u03b2_297_, lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_lift_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Std_IteratorLoop_finiteForIn_x27(v_m_294_, v_n_295_, v_00_u03b1_296_, v_00_u03b2_297_, v_inst_298_, v_inst_299_, v_inst_300_, v_lift_301_);
lean_dec(v_inst_298_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg___lam__0(lean_object* v_inst_303_, lean_object* v_toBind_304_, lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v_f_307_, lean_object* v_x_308_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_apply_2(v_inst_303_, lean_box(0), v_x_308_);
v___x_310_ = lean_apply_4(v_toBind_304_, lean_box(0), lean_box(0), v___x_309_, v_f_307_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg___lam__3(lean_object* v_toBind_311_, lean_object* v___f_312_, lean_object* v_inst_313_, lean_object* v___f_314_, lean_object* v_00_u03b3_315_, lean_object* v_it_316_, lean_object* v_init_317_, lean_object* v_f_318_){
_start:
{
lean_object* v___f_319_; lean_object* v___x_320_; 
v___f_319_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1), 6, 3);
lean_closure_set(v___f_319_, 0, v_f_318_);
lean_closure_set(v___f_319_, 1, v_toBind_311_);
lean_closure_set(v___f_319_, 2, v___f_312_);
v___x_320_ = lean_apply_6(v_inst_313_, v___f_314_, lean_box(0), lean_box(0), v_it_316_, v_init_317_, v___f_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg(lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_inst_323_){
_start:
{
lean_object* v_toApplicative_324_; lean_object* v_toBind_325_; lean_object* v_toPure_326_; lean_object* v___f_327_; lean_object* v___f_328_; lean_object* v___f_329_; 
v_toApplicative_324_ = lean_ctor_get(v_inst_322_, 0);
lean_inc_ref(v_toApplicative_324_);
v_toBind_325_ = lean_ctor_get(v_inst_322_, 1);
lean_inc(v_toBind_325_);
lean_dec_ref(v_inst_322_);
v_toPure_326_ = lean_ctor_get(v_toApplicative_324_, 1);
lean_inc(v_toPure_326_);
lean_dec_ref(v_toApplicative_324_);
lean_inc(v_toBind_325_);
v___f_327_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_327_, 0, v_inst_323_);
lean_closure_set(v___f_327_, 1, v_toBind_325_);
v___f_328_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_328_, 0, v_toPure_326_);
v___f_329_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_329_, 0, v_toBind_325_);
lean_closure_set(v___f_329_, 1, v___f_328_);
lean_closure_set(v___f_329_, 2, v_inst_321_);
lean_closure_set(v___f_329_, 3, v___f_327_);
return v___f_329_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27(lean_object* v_m_330_, lean_object* v_n_331_, lean_object* v_00_u03b1_332_, lean_object* v_00_u03b2_333_, lean_object* v_inst_334_, lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_inst_337_){
_start:
{
lean_object* v_toApplicative_338_; lean_object* v_toBind_339_; lean_object* v_toPure_340_; lean_object* v___f_341_; lean_object* v___f_342_; lean_object* v___f_343_; 
v_toApplicative_338_ = lean_ctor_get(v_inst_336_, 0);
lean_inc_ref(v_toApplicative_338_);
v_toBind_339_ = lean_ctor_get(v_inst_336_, 1);
lean_inc(v_toBind_339_);
lean_dec_ref(v_inst_336_);
v_toPure_340_ = lean_ctor_get(v_toApplicative_338_, 1);
lean_inc(v_toPure_340_);
lean_dec_ref(v_toApplicative_338_);
lean_inc(v_toBind_339_);
v___f_341_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_341_, 0, v_inst_337_);
lean_closure_set(v___f_341_, 1, v_toBind_339_);
v___f_342_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_342_, 0, v_toPure_340_);
v___f_343_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_343_, 0, v_toBind_339_);
lean_closure_set(v___f_343_, 1, v___f_342_);
lean_closure_set(v___f_343_, 2, v_inst_335_);
lean_closure_set(v___f_343_, 3, v___f_341_);
return v___f_343_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___boxed(lean_object* v_m_344_, lean_object* v_n_345_, lean_object* v_00_u03b1_346_, lean_object* v_00_u03b2_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_inst_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_IterM_instForIn_x27(v_m_344_, v_n_345_, v_00_u03b1_346_, v_00_u03b2_347_, v_inst_348_, v_inst_349_, v_inst_350_, v_inst_351_);
lean_dec(v_inst_348_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop___redArg(lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_inst_355_){
_start:
{
lean_object* v_toApplicative_356_; lean_object* v_toBind_357_; lean_object* v_toPure_358_; lean_object* v___f_359_; lean_object* v___f_360_; lean_object* v___f_361_; lean_object* v___f_362_; 
v_toApplicative_356_ = lean_ctor_get(v_inst_355_, 0);
lean_inc_ref(v_toApplicative_356_);
v_toBind_357_ = lean_ctor_get(v_inst_355_, 1);
lean_inc(v_toBind_357_);
lean_dec_ref(v_inst_355_);
v_toPure_358_ = lean_ctor_get(v_toApplicative_356_, 1);
lean_inc(v_toPure_358_);
lean_dec_ref(v_toApplicative_356_);
lean_inc(v_toBind_357_);
v___f_359_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_359_, 0, v_inst_354_);
lean_closure_set(v___f_359_, 1, v_toBind_357_);
v___f_360_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_360_, 0, v_toPure_358_);
v___f_361_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_361_, 0, v_toBind_357_);
lean_closure_set(v___f_361_, 1, v___f_360_);
lean_closure_set(v___f_361_, 2, v_inst_353_);
lean_closure_set(v___f_361_, 3, v___f_359_);
v___f_362_ = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(v___f_362_, 0, v___f_361_);
return v___f_362_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop(lean_object* v_m_363_, lean_object* v_n_364_, lean_object* v_00_u03b1_365_, lean_object* v_00_u03b2_366_, lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_inst_369_, lean_object* v_inst_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Std_IterM_instForInOfIteratorLoop___redArg(v_inst_368_, v_inst_369_, v_inst_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop___boxed(lean_object* v_m_372_, lean_object* v_n_373_, lean_object* v_00_u03b1_374_, lean_object* v_00_u03b2_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_inst_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Std_IterM_instForInOfIteratorLoop(v_m_372_, v_n_373_, v_00_u03b1_374_, v_00_u03b2_375_, v_inst_376_, v_inst_377_, v_inst_378_, v_inst_379_);
lean_dec(v_inst_376_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___redArg___lam__3(lean_object* v_toBind_381_, lean_object* v___f_382_, lean_object* v_inst_383_, lean_object* v___f_384_, lean_object* v_00_u03b2_385_, lean_object* v_it_386_, lean_object* v_init_387_, lean_object* v_f_388_){
_start:
{
lean_object* v___f_389_; lean_object* v___x_390_; 
v___f_389_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1), 6, 3);
lean_closure_set(v___f_389_, 0, v_f_388_);
lean_closure_set(v___f_389_, 1, v_toBind_381_);
lean_closure_set(v___f_389_, 2, v___f_382_);
v___x_390_ = lean_apply_6(v_inst_383_, v___f_384_, lean_box(0), lean_box(0), v_it_386_, v_init_387_, v___f_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___redArg(lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_inst_393_){
_start:
{
lean_object* v_toApplicative_394_; lean_object* v_toBind_395_; lean_object* v_toPure_396_; lean_object* v___f_397_; lean_object* v___f_398_; lean_object* v___f_399_; 
v_toApplicative_394_ = lean_ctor_get(v_inst_393_, 0);
lean_inc_ref(v_toApplicative_394_);
v_toBind_395_ = lean_ctor_get(v_inst_393_, 1);
lean_inc(v_toBind_395_);
lean_dec_ref(v_inst_393_);
v_toPure_396_ = lean_ctor_get(v_toApplicative_394_, 1);
lean_inc(v_toPure_396_);
lean_dec_ref(v_toApplicative_394_);
lean_inc(v_toBind_395_);
v___f_397_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_397_, 0, v_inst_392_);
lean_closure_set(v___f_397_, 1, v_toBind_395_);
v___f_398_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_398_, 0, v_toPure_396_);
v___f_399_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_399_, 0, v_toBind_395_);
lean_closure_set(v___f_399_, 1, v___f_398_);
lean_closure_set(v___f_399_, 2, v_inst_391_);
lean_closure_set(v___f_399_, 3, v___f_397_);
return v___f_399_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27(lean_object* v_m_400_, lean_object* v_n_401_, lean_object* v_00_u03b1_402_, lean_object* v_00_u03b2_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_inst_407_){
_start:
{
lean_object* v_toApplicative_408_; lean_object* v_toBind_409_; lean_object* v_toPure_410_; lean_object* v___f_411_; lean_object* v___f_412_; lean_object* v___f_413_; 
v_toApplicative_408_ = lean_ctor_get(v_inst_407_, 0);
lean_inc_ref(v_toApplicative_408_);
v_toBind_409_ = lean_ctor_get(v_inst_407_, 1);
lean_inc(v_toBind_409_);
lean_dec_ref(v_inst_407_);
v_toPure_410_ = lean_ctor_get(v_toApplicative_408_, 1);
lean_inc(v_toPure_410_);
lean_dec_ref(v_toApplicative_408_);
lean_inc(v_toBind_409_);
v___f_411_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_411_, 0, v_inst_406_);
lean_closure_set(v___f_411_, 1, v_toBind_409_);
v___f_412_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_412_, 0, v_toPure_410_);
v___f_413_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_413_, 0, v_toBind_409_);
lean_closure_set(v___f_413_, 1, v___f_412_);
lean_closure_set(v___f_413_, 2, v_inst_405_);
lean_closure_set(v___f_413_, 3, v___f_411_);
return v___f_413_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___boxed(lean_object* v_m_414_, lean_object* v_n_415_, lean_object* v_00_u03b1_416_, lean_object* v_00_u03b2_417_, lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_inst_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Std_IterM_Partial_instForIn_x27(v_m_414_, v_n_415_, v_00_u03b1_416_, v_00_u03b2_417_, v_inst_418_, v_inst_419_, v_inst_420_, v_inst_421_);
lean_dec(v_inst_418_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27___redArg(lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_inst_425_){
_start:
{
lean_object* v_toApplicative_426_; lean_object* v_toBind_427_; lean_object* v_toPure_428_; lean_object* v___f_429_; lean_object* v___f_430_; lean_object* v___f_431_; 
v_toApplicative_426_ = lean_ctor_get(v_inst_425_, 0);
lean_inc_ref(v_toApplicative_426_);
v_toBind_427_ = lean_ctor_get(v_inst_425_, 1);
lean_inc(v_toBind_427_);
lean_dec_ref(v_inst_425_);
v_toPure_428_ = lean_ctor_get(v_toApplicative_426_, 1);
lean_inc(v_toPure_428_);
lean_dec_ref(v_toApplicative_426_);
lean_inc(v_toBind_427_);
v___f_429_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_429_, 0, v_inst_424_);
lean_closure_set(v___f_429_, 1, v_toBind_427_);
v___f_430_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_430_, 0, v_toPure_428_);
v___f_431_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_431_, 0, v_toBind_427_);
lean_closure_set(v___f_431_, 1, v___f_430_);
lean_closure_set(v___f_431_, 2, v_inst_423_);
lean_closure_set(v___f_431_, 3, v___f_429_);
return v___f_431_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27(lean_object* v_m_432_, lean_object* v_n_433_, lean_object* v_00_u03b1_434_, lean_object* v_00_u03b2_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_inst_440_){
_start:
{
lean_object* v_toApplicative_441_; lean_object* v_toBind_442_; lean_object* v_toPure_443_; lean_object* v___f_444_; lean_object* v___f_445_; lean_object* v___f_446_; 
v_toApplicative_441_ = lean_ctor_get(v_inst_439_, 0);
lean_inc_ref(v_toApplicative_441_);
v_toBind_442_ = lean_ctor_get(v_inst_439_, 1);
lean_inc(v_toBind_442_);
lean_dec_ref(v_inst_439_);
v_toPure_443_ = lean_ctor_get(v_toApplicative_441_, 1);
lean_inc(v_toPure_443_);
lean_dec_ref(v_toApplicative_441_);
lean_inc(v_toBind_442_);
v___f_444_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_444_, 0, v_inst_438_);
lean_closure_set(v___f_444_, 1, v_toBind_442_);
v___f_445_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_445_, 0, v_toPure_443_);
v___f_446_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_446_, 0, v_toBind_442_);
lean_closure_set(v___f_446_, 1, v___f_445_);
lean_closure_set(v___f_446_, 2, v_inst_437_);
lean_closure_set(v___f_446_, 3, v___f_444_);
return v___f_446_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27___boxed(lean_object* v_m_447_, lean_object* v_n_448_, lean_object* v_00_u03b1_449_, lean_object* v_00_u03b2_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_inst_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Std_IterM_Total_instForIn_x27(v_m_447_, v_n_448_, v_00_u03b1_449_, v_00_u03b2_450_, v_inst_451_, v_inst_452_, v_inst_453_, v_inst_454_, v_inst_455_);
lean_dec(v_inst_451_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop___redArg(lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_inst_459_){
_start:
{
lean_object* v_toApplicative_460_; lean_object* v_toBind_461_; lean_object* v_toPure_462_; lean_object* v___f_463_; lean_object* v___f_464_; lean_object* v___f_465_; lean_object* v___f_466_; 
v_toApplicative_460_ = lean_ctor_get(v_inst_459_, 0);
lean_inc_ref(v_toApplicative_460_);
v_toBind_461_ = lean_ctor_get(v_inst_459_, 1);
lean_inc(v_toBind_461_);
lean_dec_ref(v_inst_459_);
v_toPure_462_ = lean_ctor_get(v_toApplicative_460_, 1);
lean_inc(v_toPure_462_);
lean_dec_ref(v_toApplicative_460_);
lean_inc(v_toBind_461_);
v___f_463_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_463_, 0, v_inst_458_);
lean_closure_set(v___f_463_, 1, v_toBind_461_);
v___f_464_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_464_, 0, v_toPure_462_);
v___f_465_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_465_, 0, v_toBind_461_);
lean_closure_set(v___f_465_, 1, v___f_464_);
lean_closure_set(v___f_465_, 2, v_inst_457_);
lean_closure_set(v___f_465_, 3, v___f_463_);
v___f_466_ = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(v___f_466_, 0, v___f_465_);
return v___f_466_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop(lean_object* v_m_467_, lean_object* v_n_468_, lean_object* v_00_u03b1_469_, lean_object* v_00_u03b2_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_inst_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_IterM_Partial_instForInOfIteratorLoop___redArg(v_inst_472_, v_inst_473_, v_inst_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop___boxed(lean_object* v_m_476_, lean_object* v_n_477_, lean_object* v_00_u03b1_478_, lean_object* v_00_u03b2_479_, lean_object* v_inst_480_, lean_object* v_inst_481_, lean_object* v_inst_482_, lean_object* v_inst_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Std_IterM_Partial_instForInOfIteratorLoop(v_m_476_, v_n_477_, v_00_u03b1_478_, v_00_u03b2_479_, v_inst_480_, v_inst_481_, v_inst_482_, v_inst_483_);
lean_dec(v_inst_480_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___redArg(lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_inst_487_){
_start:
{
lean_object* v_toApplicative_488_; lean_object* v_toBind_489_; lean_object* v_toPure_490_; lean_object* v___f_491_; lean_object* v___f_492_; lean_object* v___f_493_; lean_object* v___f_494_; 
v_toApplicative_488_ = lean_ctor_get(v_inst_487_, 0);
lean_inc_ref(v_toApplicative_488_);
v_toBind_489_ = lean_ctor_get(v_inst_487_, 1);
lean_inc(v_toBind_489_);
lean_dec_ref(v_inst_487_);
v_toPure_490_ = lean_ctor_get(v_toApplicative_488_, 1);
lean_inc(v_toPure_490_);
lean_dec_ref(v_toApplicative_488_);
lean_inc(v_toBind_489_);
v___f_491_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_491_, 0, v_inst_486_);
lean_closure_set(v___f_491_, 1, v_toBind_489_);
v___f_492_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_492_, 0, v_toPure_490_);
v___f_493_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_493_, 0, v_toBind_489_);
lean_closure_set(v___f_493_, 1, v___f_492_);
lean_closure_set(v___f_493_, 2, v_inst_485_);
lean_closure_set(v___f_493_, 3, v___f_491_);
v___f_494_ = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(v___f_494_, 0, v___f_493_);
return v___f_494_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite(lean_object* v_m_495_, lean_object* v_n_496_, lean_object* v_00_u03b1_497_, lean_object* v_00_u03b2_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_inst_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___redArg(v_inst_500_, v_inst_501_, v_inst_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___boxed(lean_object* v_m_505_, lean_object* v_n_506_, lean_object* v_00_u03b1_507_, lean_object* v_00_u03b2_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_inst_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite(v_m_505_, v_n_506_, v_00_u03b1_507_, v_00_u03b2_508_, v_inst_509_, v_inst_510_, v_inst_511_, v_inst_512_, v_inst_513_);
lean_dec(v_inst_509_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1(lean_object* v_toPure_515_, lean_object* v_____do__lift_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = lean_apply_2(v_toPure_515_, lean_box(0), v_____do__lift_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__0(lean_object* v___x_518_, lean_object* v_toPure_519_, lean_object* v_____r_520_){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_518_);
v___x_522_ = lean_apply_2(v_toPure_519_, lean_box(0), v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__2(lean_object* v_f_523_, lean_object* v_toBind_524_, lean_object* v___f_525_, lean_object* v___f_526_, lean_object* v_x1_527_, lean_object* v_x2_528_, lean_object* v_x3_529_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = lean_apply_1(v_f_523_, v_x1_527_);
lean_inc(v_toBind_524_);
v___x_531_ = lean_apply_4(v_toBind_524_, lean_box(0), lean_box(0), v___x_530_, v___f_525_);
v___x_532_ = lean_apply_4(v_toBind_524_, lean_box(0), lean_box(0), v___x_531_, v___f_526_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3(lean_object* v_toPure_533_, lean_object* v_toBind_534_, lean_object* v___f_535_, lean_object* v_inst_536_, lean_object* v___f_537_, lean_object* v_it_538_, lean_object* v_f_539_){
_start:
{
lean_object* v___x_540_; lean_object* v___f_541_; lean_object* v___f_542_; lean_object* v___x_543_; 
v___x_540_ = lean_box(0);
v___f_541_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__0), 3, 2);
lean_closure_set(v___f_541_, 0, v___x_540_);
lean_closure_set(v___f_541_, 1, v_toPure_533_);
v___f_542_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__2), 7, 4);
lean_closure_set(v___f_542_, 0, v_f_539_);
lean_closure_set(v___f_542_, 1, v_toBind_534_);
lean_closure_set(v___f_542_, 2, v___f_541_);
lean_closure_set(v___f_542_, 3, v___f_535_);
v___x_543_ = lean_apply_6(v_inst_536_, v___f_537_, lean_box(0), lean_box(0), v_it_538_, v___x_540_, v___f_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg(lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_inst_546_){
_start:
{
lean_object* v_toApplicative_547_; lean_object* v_toBind_548_; lean_object* v_toPure_549_; lean_object* v___f_550_; lean_object* v___f_551_; lean_object* v___f_552_; 
v_toApplicative_547_ = lean_ctor_get(v_inst_545_, 0);
lean_inc_ref(v_toApplicative_547_);
v_toBind_548_ = lean_ctor_get(v_inst_545_, 1);
lean_inc(v_toBind_548_);
lean_dec_ref(v_inst_545_);
v_toPure_549_ = lean_ctor_get(v_toApplicative_547_, 1);
lean_inc(v_toPure_549_);
lean_dec_ref(v_toApplicative_547_);
lean_inc(v_toBind_548_);
v___f_550_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_550_, 0, v_inst_546_);
lean_closure_set(v___f_550_, 1, v_toBind_548_);
lean_inc(v_toPure_549_);
v___f_551_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_551_, 0, v_toPure_549_);
v___f_552_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3), 7, 5);
lean_closure_set(v___f_552_, 0, v_toPure_549_);
lean_closure_set(v___f_552_, 1, v_toBind_548_);
lean_closure_set(v___f_552_, 2, v___f_551_);
lean_closure_set(v___f_552_, 3, v_inst_544_);
lean_closure_set(v___f_552_, 4, v___f_550_);
return v___f_552_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop(lean_object* v_m_553_, lean_object* v_n_554_, lean_object* v_00_u03b1_555_, lean_object* v_00_u03b2_556_, lean_object* v_inst_557_, lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_inst_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Std_IterM_instForMOfIteratorLoop___redArg(v_inst_558_, v_inst_559_, v_inst_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___boxed(lean_object* v_m_562_, lean_object* v_n_563_, lean_object* v_00_u03b1_564_, lean_object* v_00_u03b2_565_, lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_inst_568_, lean_object* v_inst_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_IterM_instForMOfIteratorLoop(v_m_562_, v_n_563_, v_00_u03b1_564_, v_00_u03b2_565_, v_inst_566_, v_inst_567_, v_inst_568_, v_inst_569_);
lean_dec(v_inst_566_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop___redArg(lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_inst_573_){
_start:
{
lean_object* v_toApplicative_574_; lean_object* v_toBind_575_; lean_object* v_toPure_576_; lean_object* v___f_577_; lean_object* v___f_578_; lean_object* v___f_579_; 
v_toApplicative_574_ = lean_ctor_get(v_inst_571_, 0);
lean_inc_ref(v_toApplicative_574_);
v_toBind_575_ = lean_ctor_get(v_inst_571_, 1);
lean_inc(v_toBind_575_);
lean_dec_ref(v_inst_571_);
v_toPure_576_ = lean_ctor_get(v_toApplicative_574_, 1);
lean_inc(v_toPure_576_);
lean_dec_ref(v_toApplicative_574_);
lean_inc(v_toBind_575_);
v___f_577_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_577_, 0, v_inst_573_);
lean_closure_set(v___f_577_, 1, v_toBind_575_);
lean_inc(v_toPure_576_);
v___f_578_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_578_, 0, v_toPure_576_);
v___f_579_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3), 7, 5);
lean_closure_set(v___f_579_, 0, v_toPure_576_);
lean_closure_set(v___f_579_, 1, v_toBind_575_);
lean_closure_set(v___f_579_, 2, v___f_578_);
lean_closure_set(v___f_579_, 3, v_inst_572_);
lean_closure_set(v___f_579_, 4, v___f_577_);
return v___f_579_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop(lean_object* v_m_580_, lean_object* v_n_581_, lean_object* v_00_u03b1_582_, lean_object* v_00_u03b2_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Std_IterM_Partial_instForMOfItreratorLoop___redArg(v_inst_584_, v_inst_586_, v_inst_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop___boxed(lean_object* v_m_589_, lean_object* v_n_590_, lean_object* v_00_u03b1_591_, lean_object* v_00_u03b2_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_inst_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Std_IterM_Partial_instForMOfItreratorLoop(v_m_589_, v_n_590_, v_00_u03b1_591_, v_00_u03b2_592_, v_inst_593_, v_inst_594_, v_inst_595_, v_inst_596_);
lean_dec(v_inst_594_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___redArg(lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_inst_600_){
_start:
{
lean_object* v_toApplicative_601_; lean_object* v_toBind_602_; lean_object* v_toPure_603_; lean_object* v___f_604_; lean_object* v___f_605_; lean_object* v___f_606_; 
v_toApplicative_601_ = lean_ctor_get(v_inst_599_, 0);
lean_inc_ref(v_toApplicative_601_);
v_toBind_602_ = lean_ctor_get(v_inst_599_, 1);
lean_inc(v_toBind_602_);
lean_dec_ref(v_inst_599_);
v_toPure_603_ = lean_ctor_get(v_toApplicative_601_, 1);
lean_inc(v_toPure_603_);
lean_dec_ref(v_toApplicative_601_);
lean_inc(v_toBind_602_);
v___f_604_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_604_, 0, v_inst_600_);
lean_closure_set(v___f_604_, 1, v_toBind_602_);
lean_inc(v_toPure_603_);
v___f_605_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_605_, 0, v_toPure_603_);
v___f_606_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3), 7, 5);
lean_closure_set(v___f_606_, 0, v_toPure_603_);
lean_closure_set(v___f_606_, 1, v_toBind_602_);
lean_closure_set(v___f_606_, 2, v___f_605_);
lean_closure_set(v___f_606_, 3, v_inst_598_);
lean_closure_set(v___f_606_, 4, v___f_604_);
return v___f_606_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite(lean_object* v_m_607_, lean_object* v_n_608_, lean_object* v_00_u03b1_609_, lean_object* v_00_u03b2_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_inst_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___redArg(v_inst_612_, v_inst_613_, v_inst_614_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___boxed(lean_object* v_m_617_, lean_object* v_n_618_, lean_object* v_00_u03b1_619_, lean_object* v_00_u03b2_620_, lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_inst_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite(v_m_617_, v_n_618_, v_00_u03b1_619_, v_00_u03b2_620_, v_inst_621_, v_inst_622_, v_inst_623_, v_inst_624_, v_inst_625_);
lean_dec(v_inst_621_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg___lam__0(lean_object* v_a_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v_a_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg___lam__3(lean_object* v_toFunctor_629_, lean_object* v_f_630_, lean_object* v___f_631_, lean_object* v_toBind_632_, lean_object* v___f_633_, lean_object* v_x1_634_, lean_object* v_x2_635_, lean_object* v_x3_636_){
_start:
{
lean_object* v_map_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v_map_637_ = lean_ctor_get(v_toFunctor_629_, 0);
lean_inc(v_map_637_);
lean_dec_ref(v_toFunctor_629_);
v___x_638_ = lean_apply_2(v_f_630_, v_x3_636_, v_x1_634_);
v___x_639_ = lean_apply_4(v_map_637_, lean_box(0), lean_box(0), v___f_631_, v___x_638_);
v___x_640_ = lean_apply_4(v_toBind_632_, lean_box(0), lean_box(0), v___x_639_, v___f_633_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg(lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_f_645_, lean_object* v_init_646_, lean_object* v_it_647_){
_start:
{
lean_object* v_toApplicative_648_; lean_object* v_toBind_649_; lean_object* v_toFunctor_650_; lean_object* v_toPure_651_; lean_object* v___f_652_; lean_object* v___f_653_; lean_object* v___f_654_; lean_object* v___f_655_; lean_object* v___x_656_; 
v_toApplicative_648_ = lean_ctor_get(v_inst_642_, 0);
lean_inc_ref(v_toApplicative_648_);
v_toBind_649_ = lean_ctor_get(v_inst_642_, 1);
lean_inc(v_toBind_649_);
lean_dec_ref(v_inst_642_);
v_toFunctor_650_ = lean_ctor_get(v_toApplicative_648_, 0);
lean_inc_ref(v_toFunctor_650_);
v_toPure_651_ = lean_ctor_get(v_toApplicative_648_, 1);
lean_inc(v_toPure_651_);
lean_dec_ref(v_toApplicative_648_);
v___f_652_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
lean_inc(v_toBind_649_);
v___f_653_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_653_, 0, v_inst_644_);
lean_closure_set(v___f_653_, 1, v_toBind_649_);
v___f_654_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_654_, 0, v_toPure_651_);
v___f_655_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_655_, 0, v_toFunctor_650_);
lean_closure_set(v___f_655_, 1, v_f_645_);
lean_closure_set(v___f_655_, 2, v___f_652_);
lean_closure_set(v___f_655_, 3, v_toBind_649_);
lean_closure_set(v___f_655_, 4, v___f_654_);
v___x_656_ = lean_apply_6(v_inst_643_, v___f_653_, lean_box(0), lean_box(0), v_it_647_, v_init_646_, v___f_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM(lean_object* v_m_657_, lean_object* v_n_658_, lean_object* v_inst_659_, lean_object* v_00_u03b1_660_, lean_object* v_00_u03b2_661_, lean_object* v_00_u03b3_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_f_666_, lean_object* v_init_667_, lean_object* v_it_668_){
_start:
{
lean_object* v_toApplicative_669_; lean_object* v_toBind_670_; lean_object* v_toFunctor_671_; lean_object* v_toPure_672_; lean_object* v___f_673_; lean_object* v___f_674_; lean_object* v___f_675_; lean_object* v___f_676_; lean_object* v___x_677_; 
v_toApplicative_669_ = lean_ctor_get(v_inst_659_, 0);
lean_inc_ref(v_toApplicative_669_);
v_toBind_670_ = lean_ctor_get(v_inst_659_, 1);
lean_inc(v_toBind_670_);
lean_dec_ref(v_inst_659_);
v_toFunctor_671_ = lean_ctor_get(v_toApplicative_669_, 0);
lean_inc_ref(v_toFunctor_671_);
v_toPure_672_ = lean_ctor_get(v_toApplicative_669_, 1);
lean_inc(v_toPure_672_);
lean_dec_ref(v_toApplicative_669_);
v___f_673_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
lean_inc(v_toBind_670_);
v___f_674_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_674_, 0, v_inst_665_);
lean_closure_set(v___f_674_, 1, v_toBind_670_);
v___f_675_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_675_, 0, v_toPure_672_);
v___f_676_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_676_, 0, v_toFunctor_671_);
lean_closure_set(v___f_676_, 1, v_f_666_);
lean_closure_set(v___f_676_, 2, v___f_673_);
lean_closure_set(v___f_676_, 3, v_toBind_670_);
lean_closure_set(v___f_676_, 4, v___f_675_);
v___x_677_ = lean_apply_6(v_inst_664_, v___f_674_, lean_box(0), lean_box(0), v_it_668_, v_init_667_, v___f_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___boxed(lean_object* v_m_678_, lean_object* v_n_679_, lean_object* v_inst_680_, lean_object* v_00_u03b1_681_, lean_object* v_00_u03b2_682_, lean_object* v_00_u03b3_683_, lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_f_687_, lean_object* v_init_688_, lean_object* v_it_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Std_IterM_foldM(v_m_678_, v_n_679_, v_inst_680_, v_00_u03b1_681_, v_00_u03b2_682_, v_00_u03b3_683_, v_inst_684_, v_inst_685_, v_inst_686_, v_f_687_, v_init_688_, v_it_689_);
lean_dec(v_inst_684_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM___redArg(lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_f_694_, lean_object* v_init_695_, lean_object* v_it_696_){
_start:
{
lean_object* v_toApplicative_697_; lean_object* v_toBind_698_; lean_object* v_toFunctor_699_; lean_object* v_toPure_700_; lean_object* v___f_701_; lean_object* v___f_702_; lean_object* v___f_703_; lean_object* v___f_704_; lean_object* v___x_705_; 
v_toApplicative_697_ = lean_ctor_get(v_inst_691_, 0);
lean_inc_ref(v_toApplicative_697_);
v_toBind_698_ = lean_ctor_get(v_inst_691_, 1);
lean_inc(v_toBind_698_);
lean_dec_ref(v_inst_691_);
v_toFunctor_699_ = lean_ctor_get(v_toApplicative_697_, 0);
lean_inc_ref(v_toFunctor_699_);
v_toPure_700_ = lean_ctor_get(v_toApplicative_697_, 1);
lean_inc(v_toPure_700_);
lean_dec_ref(v_toApplicative_697_);
v___f_701_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
lean_inc(v_toBind_698_);
v___f_702_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_702_, 0, v_inst_693_);
lean_closure_set(v___f_702_, 1, v_toBind_698_);
v___f_703_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_703_, 0, v_toPure_700_);
v___f_704_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_704_, 0, v_toFunctor_699_);
lean_closure_set(v___f_704_, 1, v_f_694_);
lean_closure_set(v___f_704_, 2, v___f_701_);
lean_closure_set(v___f_704_, 3, v_toBind_698_);
lean_closure_set(v___f_704_, 4, v___f_703_);
v___x_705_ = lean_apply_6(v_inst_692_, v___f_702_, lean_box(0), lean_box(0), v_it_696_, v_init_695_, v___f_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM(lean_object* v_m_706_, lean_object* v_n_707_, lean_object* v_inst_708_, lean_object* v_00_u03b1_709_, lean_object* v_00_u03b2_710_, lean_object* v_00_u03b3_711_, lean_object* v_inst_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_f_715_, lean_object* v_init_716_, lean_object* v_it_717_){
_start:
{
lean_object* v_toApplicative_718_; lean_object* v_toBind_719_; lean_object* v_toFunctor_720_; lean_object* v_toPure_721_; lean_object* v___f_722_; lean_object* v___f_723_; lean_object* v___f_724_; lean_object* v___f_725_; lean_object* v___x_726_; 
v_toApplicative_718_ = lean_ctor_get(v_inst_708_, 0);
lean_inc_ref(v_toApplicative_718_);
v_toBind_719_ = lean_ctor_get(v_inst_708_, 1);
lean_inc(v_toBind_719_);
lean_dec_ref(v_inst_708_);
v_toFunctor_720_ = lean_ctor_get(v_toApplicative_718_, 0);
lean_inc_ref(v_toFunctor_720_);
v_toPure_721_ = lean_ctor_get(v_toApplicative_718_, 1);
lean_inc(v_toPure_721_);
lean_dec_ref(v_toApplicative_718_);
v___f_722_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
lean_inc(v_toBind_719_);
v___f_723_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_723_, 0, v_inst_714_);
lean_closure_set(v___f_723_, 1, v_toBind_719_);
v___f_724_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_724_, 0, v_toPure_721_);
v___f_725_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_725_, 0, v_toFunctor_720_);
lean_closure_set(v___f_725_, 1, v_f_715_);
lean_closure_set(v___f_725_, 2, v___f_722_);
lean_closure_set(v___f_725_, 3, v_toBind_719_);
lean_closure_set(v___f_725_, 4, v___f_724_);
v___x_726_ = lean_apply_6(v_inst_713_, v___f_723_, lean_box(0), lean_box(0), v_it_717_, v_init_716_, v___f_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM___boxed(lean_object* v_m_727_, lean_object* v_n_728_, lean_object* v_inst_729_, lean_object* v_00_u03b1_730_, lean_object* v_00_u03b2_731_, lean_object* v_00_u03b3_732_, lean_object* v_inst_733_, lean_object* v_inst_734_, lean_object* v_inst_735_, lean_object* v_f_736_, lean_object* v_init_737_, lean_object* v_it_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_IterM_Partial_foldM(v_m_727_, v_n_728_, v_inst_729_, v_00_u03b1_730_, v_00_u03b2_731_, v_00_u03b3_732_, v_inst_733_, v_inst_734_, v_inst_735_, v_f_736_, v_init_737_, v_it_738_);
lean_dec(v_inst_733_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM___redArg(lean_object* v_inst_740_, lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_f_743_, lean_object* v_init_744_, lean_object* v_it_745_){
_start:
{
lean_object* v_toApplicative_746_; lean_object* v_toBind_747_; lean_object* v_toFunctor_748_; lean_object* v_toPure_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___f_752_; lean_object* v___f_753_; lean_object* v___x_754_; 
v_toApplicative_746_ = lean_ctor_get(v_inst_740_, 0);
lean_inc_ref(v_toApplicative_746_);
v_toBind_747_ = lean_ctor_get(v_inst_740_, 1);
lean_inc(v_toBind_747_);
lean_dec_ref(v_inst_740_);
v_toFunctor_748_ = lean_ctor_get(v_toApplicative_746_, 0);
lean_inc_ref(v_toFunctor_748_);
v_toPure_749_ = lean_ctor_get(v_toApplicative_746_, 1);
lean_inc(v_toPure_749_);
lean_dec_ref(v_toApplicative_746_);
v___f_750_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
lean_inc(v_toBind_747_);
v___f_751_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_751_, 0, v_inst_742_);
lean_closure_set(v___f_751_, 1, v_toBind_747_);
v___f_752_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_752_, 0, v_toPure_749_);
v___f_753_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_753_, 0, v_toFunctor_748_);
lean_closure_set(v___f_753_, 1, v_f_743_);
lean_closure_set(v___f_753_, 2, v___f_750_);
lean_closure_set(v___f_753_, 3, v_toBind_747_);
lean_closure_set(v___f_753_, 4, v___f_752_);
v___x_754_ = lean_apply_6(v_inst_741_, v___f_751_, lean_box(0), lean_box(0), v_it_745_, v_init_744_, v___f_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM(lean_object* v_m_755_, lean_object* v_n_756_, lean_object* v_inst_757_, lean_object* v_00_u03b1_758_, lean_object* v_00_u03b2_759_, lean_object* v_00_u03b3_760_, lean_object* v_inst_761_, lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_inst_764_, lean_object* v_f_765_, lean_object* v_init_766_, lean_object* v_it_767_){
_start:
{
lean_object* v_toApplicative_768_; lean_object* v_toBind_769_; lean_object* v_toFunctor_770_; lean_object* v_toPure_771_; lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___x_776_; 
v_toApplicative_768_ = lean_ctor_get(v_inst_757_, 0);
lean_inc_ref(v_toApplicative_768_);
v_toBind_769_ = lean_ctor_get(v_inst_757_, 1);
lean_inc(v_toBind_769_);
lean_dec_ref(v_inst_757_);
v_toFunctor_770_ = lean_ctor_get(v_toApplicative_768_, 0);
lean_inc_ref(v_toFunctor_770_);
v_toPure_771_ = lean_ctor_get(v_toApplicative_768_, 1);
lean_inc(v_toPure_771_);
lean_dec_ref(v_toApplicative_768_);
v___f_772_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
lean_inc(v_toBind_769_);
v___f_773_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_773_, 0, v_inst_763_);
lean_closure_set(v___f_773_, 1, v_toBind_769_);
v___f_774_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_774_, 0, v_toPure_771_);
v___f_775_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_775_, 0, v_toFunctor_770_);
lean_closure_set(v___f_775_, 1, v_f_765_);
lean_closure_set(v___f_775_, 2, v___f_772_);
lean_closure_set(v___f_775_, 3, v_toBind_769_);
lean_closure_set(v___f_775_, 4, v___f_774_);
v___x_776_ = lean_apply_6(v_inst_762_, v___f_773_, lean_box(0), lean_box(0), v_it_767_, v_init_766_, v___f_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM___boxed(lean_object* v_m_777_, lean_object* v_n_778_, lean_object* v_inst_779_, lean_object* v_00_u03b1_780_, lean_object* v_00_u03b2_781_, lean_object* v_00_u03b3_782_, lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_f_787_, lean_object* v_init_788_, lean_object* v_it_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Std_IterM_Total_foldM(v_m_777_, v_n_778_, v_inst_779_, v_00_u03b1_780_, v_00_u03b2_781_, v_00_u03b3_782_, v_inst_783_, v_inst_784_, v_inst_785_, v_inst_786_, v_f_787_, v_init_788_, v_it_789_);
lean_dec(v_inst_783_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg___lam__0(lean_object* v_toBind_791_, lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_f_794_, lean_object* v_x_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = lean_apply_4(v_toBind_791_, lean_box(0), lean_box(0), v_x_795_, v_f_794_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg___lam__2(lean_object* v_f_797_, lean_object* v_toPure_798_, lean_object* v_toBind_799_, lean_object* v___f_800_, lean_object* v_x1_801_, lean_object* v_x2_802_, lean_object* v_x3_803_){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_804_ = lean_apply_2(v_f_797_, v_x3_803_, v_x1_801_);
v___x_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
v___x_806_ = lean_apply_2(v_toPure_798_, lean_box(0), v___x_805_);
v___x_807_ = lean_apply_4(v_toBind_799_, lean_box(0), lean_box(0), v___x_806_, v___f_800_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg(lean_object* v_inst_808_, lean_object* v_inst_809_, lean_object* v_f_810_, lean_object* v_init_811_, lean_object* v_it_812_){
_start:
{
lean_object* v_toApplicative_813_; lean_object* v_toBind_814_; lean_object* v_toPure_815_; lean_object* v___f_816_; lean_object* v___f_817_; lean_object* v___f_818_; lean_object* v___x_819_; 
v_toApplicative_813_ = lean_ctor_get(v_inst_808_, 0);
lean_inc_ref(v_toApplicative_813_);
v_toBind_814_ = lean_ctor_get(v_inst_808_, 1);
lean_inc(v_toBind_814_);
lean_dec_ref(v_inst_808_);
v_toPure_815_ = lean_ctor_get(v_toApplicative_813_, 1);
lean_inc(v_toPure_815_);
lean_dec_ref(v_toApplicative_813_);
lean_inc(v_toBind_814_);
v___f_816_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_816_, 0, v_toBind_814_);
lean_inc(v_toPure_815_);
v___f_817_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_817_, 0, v_toPure_815_);
v___f_818_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_818_, 0, v_f_810_);
lean_closure_set(v___f_818_, 1, v_toPure_815_);
lean_closure_set(v___f_818_, 2, v_toBind_814_);
lean_closure_set(v___f_818_, 3, v___f_817_);
v___x_819_ = lean_apply_6(v_inst_809_, v___f_816_, lean_box(0), lean_box(0), v_it_812_, v_init_811_, v___f_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold(lean_object* v_m_820_, lean_object* v_00_u03b1_821_, lean_object* v_00_u03b2_822_, lean_object* v_00_u03b3_823_, lean_object* v_inst_824_, lean_object* v_inst_825_, lean_object* v_inst_826_, lean_object* v_f_827_, lean_object* v_init_828_, lean_object* v_it_829_){
_start:
{
lean_object* v_toApplicative_830_; lean_object* v_toBind_831_; lean_object* v_toPure_832_; lean_object* v___f_833_; lean_object* v___f_834_; lean_object* v___f_835_; lean_object* v___x_836_; 
v_toApplicative_830_ = lean_ctor_get(v_inst_824_, 0);
lean_inc_ref(v_toApplicative_830_);
v_toBind_831_ = lean_ctor_get(v_inst_824_, 1);
lean_inc(v_toBind_831_);
lean_dec_ref(v_inst_824_);
v_toPure_832_ = lean_ctor_get(v_toApplicative_830_, 1);
lean_inc(v_toPure_832_);
lean_dec_ref(v_toApplicative_830_);
lean_inc(v_toBind_831_);
v___f_833_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_833_, 0, v_toBind_831_);
lean_inc(v_toPure_832_);
v___f_834_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_834_, 0, v_toPure_832_);
v___f_835_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_835_, 0, v_f_827_);
lean_closure_set(v___f_835_, 1, v_toPure_832_);
lean_closure_set(v___f_835_, 2, v_toBind_831_);
lean_closure_set(v___f_835_, 3, v___f_834_);
v___x_836_ = lean_apply_6(v_inst_826_, v___f_833_, lean_box(0), lean_box(0), v_it_829_, v_init_828_, v___f_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___boxed(lean_object* v_m_837_, lean_object* v_00_u03b1_838_, lean_object* v_00_u03b2_839_, lean_object* v_00_u03b3_840_, lean_object* v_inst_841_, lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_f_844_, lean_object* v_init_845_, lean_object* v_it_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Std_IterM_fold(v_m_837_, v_00_u03b1_838_, v_00_u03b2_839_, v_00_u03b3_840_, v_inst_841_, v_inst_842_, v_inst_843_, v_f_844_, v_init_845_, v_it_846_);
lean_dec(v_inst_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold___redArg(lean_object* v_inst_848_, lean_object* v_inst_849_, lean_object* v_f_850_, lean_object* v_init_851_, lean_object* v_it_852_){
_start:
{
lean_object* v_toApplicative_853_; lean_object* v_toBind_854_; lean_object* v_toPure_855_; lean_object* v___f_856_; lean_object* v___f_857_; lean_object* v___f_858_; lean_object* v___x_859_; 
v_toApplicative_853_ = lean_ctor_get(v_inst_848_, 0);
lean_inc_ref(v_toApplicative_853_);
v_toBind_854_ = lean_ctor_get(v_inst_848_, 1);
lean_inc(v_toBind_854_);
lean_dec_ref(v_inst_848_);
v_toPure_855_ = lean_ctor_get(v_toApplicative_853_, 1);
lean_inc(v_toPure_855_);
lean_dec_ref(v_toApplicative_853_);
lean_inc(v_toBind_854_);
v___f_856_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_856_, 0, v_toBind_854_);
lean_inc(v_toPure_855_);
v___f_857_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_857_, 0, v_toPure_855_);
v___f_858_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_858_, 0, v_f_850_);
lean_closure_set(v___f_858_, 1, v_toPure_855_);
lean_closure_set(v___f_858_, 2, v_toBind_854_);
lean_closure_set(v___f_858_, 3, v___f_857_);
v___x_859_ = lean_apply_6(v_inst_849_, v___f_856_, lean_box(0), lean_box(0), v_it_852_, v_init_851_, v___f_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold(lean_object* v_m_860_, lean_object* v_00_u03b1_861_, lean_object* v_00_u03b2_862_, lean_object* v_00_u03b3_863_, lean_object* v_inst_864_, lean_object* v_inst_865_, lean_object* v_inst_866_, lean_object* v_f_867_, lean_object* v_init_868_, lean_object* v_it_869_){
_start:
{
lean_object* v_toApplicative_870_; lean_object* v_toBind_871_; lean_object* v_toPure_872_; lean_object* v___f_873_; lean_object* v___f_874_; lean_object* v___f_875_; lean_object* v___x_876_; 
v_toApplicative_870_ = lean_ctor_get(v_inst_864_, 0);
lean_inc_ref(v_toApplicative_870_);
v_toBind_871_ = lean_ctor_get(v_inst_864_, 1);
lean_inc(v_toBind_871_);
lean_dec_ref(v_inst_864_);
v_toPure_872_ = lean_ctor_get(v_toApplicative_870_, 1);
lean_inc(v_toPure_872_);
lean_dec_ref(v_toApplicative_870_);
lean_inc(v_toBind_871_);
v___f_873_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_873_, 0, v_toBind_871_);
lean_inc(v_toPure_872_);
v___f_874_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_874_, 0, v_toPure_872_);
v___f_875_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_875_, 0, v_f_867_);
lean_closure_set(v___f_875_, 1, v_toPure_872_);
lean_closure_set(v___f_875_, 2, v_toBind_871_);
lean_closure_set(v___f_875_, 3, v___f_874_);
v___x_876_ = lean_apply_6(v_inst_866_, v___f_873_, lean_box(0), lean_box(0), v_it_869_, v_init_868_, v___f_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold___boxed(lean_object* v_m_877_, lean_object* v_00_u03b1_878_, lean_object* v_00_u03b2_879_, lean_object* v_00_u03b3_880_, lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_inst_883_, lean_object* v_f_884_, lean_object* v_init_885_, lean_object* v_it_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Std_IterM_Partial_fold(v_m_877_, v_00_u03b1_878_, v_00_u03b2_879_, v_00_u03b3_880_, v_inst_881_, v_inst_882_, v_inst_883_, v_f_884_, v_init_885_, v_it_886_);
lean_dec(v_inst_882_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold___redArg(lean_object* v_inst_888_, lean_object* v_inst_889_, lean_object* v_f_890_, lean_object* v_init_891_, lean_object* v_it_892_){
_start:
{
lean_object* v_toApplicative_893_; lean_object* v_toBind_894_; lean_object* v_toPure_895_; lean_object* v___f_896_; lean_object* v___f_897_; lean_object* v___f_898_; lean_object* v___x_899_; 
v_toApplicative_893_ = lean_ctor_get(v_inst_888_, 0);
lean_inc_ref(v_toApplicative_893_);
v_toBind_894_ = lean_ctor_get(v_inst_888_, 1);
lean_inc(v_toBind_894_);
lean_dec_ref(v_inst_888_);
v_toPure_895_ = lean_ctor_get(v_toApplicative_893_, 1);
lean_inc(v_toPure_895_);
lean_dec_ref(v_toApplicative_893_);
lean_inc(v_toBind_894_);
v___f_896_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_896_, 0, v_toBind_894_);
lean_inc(v_toPure_895_);
v___f_897_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_897_, 0, v_toPure_895_);
v___f_898_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_898_, 0, v_f_890_);
lean_closure_set(v___f_898_, 1, v_toPure_895_);
lean_closure_set(v___f_898_, 2, v_toBind_894_);
lean_closure_set(v___f_898_, 3, v___f_897_);
v___x_899_ = lean_apply_6(v_inst_889_, v___f_896_, lean_box(0), lean_box(0), v_it_892_, v_init_891_, v___f_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold(lean_object* v_m_900_, lean_object* v_00_u03b1_901_, lean_object* v_00_u03b2_902_, lean_object* v_00_u03b3_903_, lean_object* v_inst_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_inst_907_, lean_object* v_f_908_, lean_object* v_init_909_, lean_object* v_it_910_){
_start:
{
lean_object* v_toApplicative_911_; lean_object* v_toBind_912_; lean_object* v_toPure_913_; lean_object* v___f_914_; lean_object* v___f_915_; lean_object* v___f_916_; lean_object* v___x_917_; 
v_toApplicative_911_ = lean_ctor_get(v_inst_904_, 0);
lean_inc_ref(v_toApplicative_911_);
v_toBind_912_ = lean_ctor_get(v_inst_904_, 1);
lean_inc(v_toBind_912_);
lean_dec_ref(v_inst_904_);
v_toPure_913_ = lean_ctor_get(v_toApplicative_911_, 1);
lean_inc(v_toPure_913_);
lean_dec_ref(v_toApplicative_911_);
lean_inc(v_toBind_912_);
v___f_914_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_914_, 0, v_toBind_912_);
lean_inc(v_toPure_913_);
v___f_915_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_915_, 0, v_toPure_913_);
v___f_916_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_916_, 0, v_f_908_);
lean_closure_set(v___f_916_, 1, v_toPure_913_);
lean_closure_set(v___f_916_, 2, v_toBind_912_);
lean_closure_set(v___f_916_, 3, v___f_915_);
v___x_917_ = lean_apply_6(v_inst_906_, v___f_914_, lean_box(0), lean_box(0), v_it_910_, v_init_909_, v___f_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold___boxed(lean_object* v_m_918_, lean_object* v_00_u03b1_919_, lean_object* v_00_u03b2_920_, lean_object* v_00_u03b3_921_, lean_object* v_inst_922_, lean_object* v_inst_923_, lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_f_926_, lean_object* v_init_927_, lean_object* v_it_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Std_IterM_Total_fold(v_m_918_, v_00_u03b1_919_, v_00_u03b2_920_, v_00_u03b3_921_, v_inst_922_, v_inst_923_, v_inst_924_, v_inst_925_, v_f_926_, v_init_927_, v_it_928_);
lean_dec(v_inst_923_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg___lam__2(lean_object* v___x_930_, lean_object* v_toPure_931_, lean_object* v_toBind_932_, lean_object* v___f_933_, lean_object* v_x1_934_, lean_object* v_x2_935_, lean_object* v_x3_936_){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_930_);
v___x_938_ = lean_apply_2(v_toPure_931_, lean_box(0), v___x_937_);
v___x_939_ = lean_apply_4(v_toBind_932_, lean_box(0), lean_box(0), v___x_938_, v___f_933_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg___lam__2___boxed(lean_object* v___x_940_, lean_object* v_toPure_941_, lean_object* v_toBind_942_, lean_object* v___f_943_, lean_object* v_x1_944_, lean_object* v_x2_945_, lean_object* v_x3_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Std_IterM_drain___redArg___lam__2(v___x_940_, v_toPure_941_, v_toBind_942_, v___f_943_, v_x1_944_, v_x2_945_, v_x3_946_);
lean_dec(v_x1_944_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg(lean_object* v_inst_948_, lean_object* v_it_949_, lean_object* v_inst_950_){
_start:
{
lean_object* v_toApplicative_951_; lean_object* v_toBind_952_; lean_object* v_toPure_953_; lean_object* v___x_954_; lean_object* v___f_955_; lean_object* v___f_956_; lean_object* v___f_957_; lean_object* v___x_958_; 
v_toApplicative_951_ = lean_ctor_get(v_inst_948_, 0);
lean_inc_ref(v_toApplicative_951_);
v_toBind_952_ = lean_ctor_get(v_inst_948_, 1);
lean_inc(v_toBind_952_);
lean_dec_ref(v_inst_948_);
v_toPure_953_ = lean_ctor_get(v_toApplicative_951_, 1);
lean_inc(v_toPure_953_);
lean_dec_ref(v_toApplicative_951_);
v___x_954_ = lean_box(0);
lean_inc(v_toBind_952_);
v___f_955_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_955_, 0, v_toBind_952_);
lean_inc(v_toPure_953_);
v___f_956_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_956_, 0, v_toPure_953_);
v___f_957_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_957_, 0, v___x_954_);
lean_closure_set(v___f_957_, 1, v_toPure_953_);
lean_closure_set(v___f_957_, 2, v_toBind_952_);
lean_closure_set(v___f_957_, 3, v___f_956_);
v___x_958_ = lean_apply_6(v_inst_950_, v___f_955_, lean_box(0), lean_box(0), v_it_949_, v___x_954_, v___f_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain(lean_object* v_00_u03b1_959_, lean_object* v_m_960_, lean_object* v_inst_961_, lean_object* v_00_u03b2_962_, lean_object* v_inst_963_, lean_object* v_it_964_, lean_object* v_inst_965_){
_start:
{
lean_object* v_toApplicative_966_; lean_object* v_toBind_967_; lean_object* v_toPure_968_; lean_object* v___x_969_; lean_object* v___f_970_; lean_object* v___f_971_; lean_object* v___f_972_; lean_object* v___x_973_; 
v_toApplicative_966_ = lean_ctor_get(v_inst_961_, 0);
lean_inc_ref(v_toApplicative_966_);
v_toBind_967_ = lean_ctor_get(v_inst_961_, 1);
lean_inc(v_toBind_967_);
lean_dec_ref(v_inst_961_);
v_toPure_968_ = lean_ctor_get(v_toApplicative_966_, 1);
lean_inc(v_toPure_968_);
lean_dec_ref(v_toApplicative_966_);
v___x_969_ = lean_box(0);
lean_inc(v_toBind_967_);
v___f_970_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_970_, 0, v_toBind_967_);
lean_inc(v_toPure_968_);
v___f_971_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_971_, 0, v_toPure_968_);
v___f_972_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_972_, 0, v___x_969_);
lean_closure_set(v___f_972_, 1, v_toPure_968_);
lean_closure_set(v___f_972_, 2, v_toBind_967_);
lean_closure_set(v___f_972_, 3, v___f_971_);
v___x_973_ = lean_apply_6(v_inst_965_, v___f_970_, lean_box(0), lean_box(0), v_it_964_, v___x_969_, v___f_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___boxed(lean_object* v_00_u03b1_974_, lean_object* v_m_975_, lean_object* v_inst_976_, lean_object* v_00_u03b2_977_, lean_object* v_inst_978_, lean_object* v_it_979_, lean_object* v_inst_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Std_IterM_drain(v_00_u03b1_974_, v_m_975_, v_inst_976_, v_00_u03b2_977_, v_inst_978_, v_it_979_, v_inst_980_);
lean_dec(v_inst_978_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain___redArg(lean_object* v_inst_982_, lean_object* v_it_983_, lean_object* v_inst_984_){
_start:
{
lean_object* v_toApplicative_985_; lean_object* v_toBind_986_; lean_object* v_toPure_987_; lean_object* v___x_988_; lean_object* v___f_989_; lean_object* v___f_990_; lean_object* v___f_991_; lean_object* v___x_992_; 
v_toApplicative_985_ = lean_ctor_get(v_inst_982_, 0);
lean_inc_ref(v_toApplicative_985_);
v_toBind_986_ = lean_ctor_get(v_inst_982_, 1);
lean_inc(v_toBind_986_);
lean_dec_ref(v_inst_982_);
v_toPure_987_ = lean_ctor_get(v_toApplicative_985_, 1);
lean_inc(v_toPure_987_);
lean_dec_ref(v_toApplicative_985_);
v___x_988_ = lean_box(0);
lean_inc(v_toBind_986_);
v___f_989_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_989_, 0, v_toBind_986_);
lean_inc(v_toPure_987_);
v___f_990_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_990_, 0, v_toPure_987_);
v___f_991_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_991_, 0, v___x_988_);
lean_closure_set(v___f_991_, 1, v_toPure_987_);
lean_closure_set(v___f_991_, 2, v_toBind_986_);
lean_closure_set(v___f_991_, 3, v___f_990_);
v___x_992_ = lean_apply_6(v_inst_984_, v___f_989_, lean_box(0), lean_box(0), v_it_983_, v___x_988_, v___f_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain(lean_object* v_00_u03b1_993_, lean_object* v_m_994_, lean_object* v_inst_995_, lean_object* v_00_u03b2_996_, lean_object* v_inst_997_, lean_object* v_it_998_, lean_object* v_inst_999_){
_start:
{
lean_object* v_toApplicative_1000_; lean_object* v_toBind_1001_; lean_object* v_toPure_1002_; lean_object* v___x_1003_; lean_object* v___f_1004_; lean_object* v___f_1005_; lean_object* v___f_1006_; lean_object* v___x_1007_; 
v_toApplicative_1000_ = lean_ctor_get(v_inst_995_, 0);
lean_inc_ref(v_toApplicative_1000_);
v_toBind_1001_ = lean_ctor_get(v_inst_995_, 1);
lean_inc(v_toBind_1001_);
lean_dec_ref(v_inst_995_);
v_toPure_1002_ = lean_ctor_get(v_toApplicative_1000_, 1);
lean_inc(v_toPure_1002_);
lean_dec_ref(v_toApplicative_1000_);
v___x_1003_ = lean_box(0);
lean_inc(v_toBind_1001_);
v___f_1004_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1004_, 0, v_toBind_1001_);
lean_inc(v_toPure_1002_);
v___f_1005_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1005_, 0, v_toPure_1002_);
v___f_1006_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1006_, 0, v___x_1003_);
lean_closure_set(v___f_1006_, 1, v_toPure_1002_);
lean_closure_set(v___f_1006_, 2, v_toBind_1001_);
lean_closure_set(v___f_1006_, 3, v___f_1005_);
v___x_1007_ = lean_apply_6(v_inst_999_, v___f_1004_, lean_box(0), lean_box(0), v_it_998_, v___x_1003_, v___f_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain___boxed(lean_object* v_00_u03b1_1008_, lean_object* v_m_1009_, lean_object* v_inst_1010_, lean_object* v_00_u03b2_1011_, lean_object* v_inst_1012_, lean_object* v_it_1013_, lean_object* v_inst_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Std_IterM_Partial_drain(v_00_u03b1_1008_, v_m_1009_, v_inst_1010_, v_00_u03b2_1011_, v_inst_1012_, v_it_1013_, v_inst_1014_);
lean_dec(v_inst_1012_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain___redArg(lean_object* v_inst_1016_, lean_object* v_it_1017_, lean_object* v_inst_1018_){
_start:
{
lean_object* v_toApplicative_1019_; lean_object* v_toBind_1020_; lean_object* v_toPure_1021_; lean_object* v___x_1022_; lean_object* v___f_1023_; lean_object* v___f_1024_; lean_object* v___f_1025_; lean_object* v___x_1026_; 
v_toApplicative_1019_ = lean_ctor_get(v_inst_1016_, 0);
lean_inc_ref(v_toApplicative_1019_);
v_toBind_1020_ = lean_ctor_get(v_inst_1016_, 1);
lean_inc(v_toBind_1020_);
lean_dec_ref(v_inst_1016_);
v_toPure_1021_ = lean_ctor_get(v_toApplicative_1019_, 1);
lean_inc(v_toPure_1021_);
lean_dec_ref(v_toApplicative_1019_);
v___x_1022_ = lean_box(0);
lean_inc(v_toBind_1020_);
v___f_1023_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1023_, 0, v_toBind_1020_);
lean_inc(v_toPure_1021_);
v___f_1024_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1024_, 0, v_toPure_1021_);
v___f_1025_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1025_, 0, v___x_1022_);
lean_closure_set(v___f_1025_, 1, v_toPure_1021_);
lean_closure_set(v___f_1025_, 2, v_toBind_1020_);
lean_closure_set(v___f_1025_, 3, v___f_1024_);
v___x_1026_ = lean_apply_6(v_inst_1018_, v___f_1023_, lean_box(0), lean_box(0), v_it_1017_, v___x_1022_, v___f_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain(lean_object* v_00_u03b1_1027_, lean_object* v_m_1028_, lean_object* v_inst_1029_, lean_object* v_00_u03b2_1030_, lean_object* v_inst_1031_, lean_object* v_inst_1032_, lean_object* v_it_1033_, lean_object* v_inst_1034_){
_start:
{
lean_object* v_toApplicative_1035_; lean_object* v_toBind_1036_; lean_object* v_toPure_1037_; lean_object* v___x_1038_; lean_object* v___f_1039_; lean_object* v___f_1040_; lean_object* v___f_1041_; lean_object* v___x_1042_; 
v_toApplicative_1035_ = lean_ctor_get(v_inst_1029_, 0);
lean_inc_ref(v_toApplicative_1035_);
v_toBind_1036_ = lean_ctor_get(v_inst_1029_, 1);
lean_inc(v_toBind_1036_);
lean_dec_ref(v_inst_1029_);
v_toPure_1037_ = lean_ctor_get(v_toApplicative_1035_, 1);
lean_inc(v_toPure_1037_);
lean_dec_ref(v_toApplicative_1035_);
v___x_1038_ = lean_box(0);
lean_inc(v_toBind_1036_);
v___f_1039_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1039_, 0, v_toBind_1036_);
lean_inc(v_toPure_1037_);
v___f_1040_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1040_, 0, v_toPure_1037_);
v___f_1041_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1041_, 0, v___x_1038_);
lean_closure_set(v___f_1041_, 1, v_toPure_1037_);
lean_closure_set(v___f_1041_, 2, v_toBind_1036_);
lean_closure_set(v___f_1041_, 3, v___f_1040_);
v___x_1042_ = lean_apply_6(v_inst_1034_, v___f_1039_, lean_box(0), lean_box(0), v_it_1033_, v___x_1038_, v___f_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain___boxed(lean_object* v_00_u03b1_1043_, lean_object* v_m_1044_, lean_object* v_inst_1045_, lean_object* v_00_u03b2_1046_, lean_object* v_inst_1047_, lean_object* v_inst_1048_, lean_object* v_it_1049_, lean_object* v_inst_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Std_IterM_Total_drain(v_00_u03b1_1043_, v_m_1044_, v_inst_1045_, v_00_u03b2_1046_, v_inst_1047_, v_inst_1048_, v_it_1049_, v_inst_1050_);
lean_dec(v_inst_1047_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__1(lean_object* v_toPure_1052_, lean_object* v_____do__lift_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = lean_apply_2(v_toPure_1052_, lean_box(0), v_____do__lift_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__0(uint8_t v___x_1055_, lean_object* v_toPure_1056_, uint8_t v_____do__lift_1057_){
_start:
{
if (v_____do__lift_1057_ == 0)
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = lean_box(v___x_1055_);
v___x_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
v___x_1060_ = lean_apply_2(v_toPure_1056_, lean_box(0), v___x_1059_);
return v___x_1060_;
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1061_ = lean_box(v_____do__lift_1057_);
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
v___x_1063_ = lean_apply_2(v_toPure_1056_, lean_box(0), v___x_1062_);
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__0___boxed(lean_object* v___x_1064_, lean_object* v_toPure_1065_, lean_object* v_____do__lift_1066_){
_start:
{
uint8_t v___x_203__boxed_1067_; uint8_t v_____do__lift_204__boxed_1068_; lean_object* v_res_1069_; 
v___x_203__boxed_1067_ = lean_unbox(v___x_1064_);
v_____do__lift_204__boxed_1068_ = lean_unbox(v_____do__lift_1066_);
v_res_1069_ = l_Std_IterM_anyM___redArg___lam__0(v___x_203__boxed_1067_, v_toPure_1065_, v_____do__lift_204__boxed_1068_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__2(lean_object* v_p_1070_, lean_object* v_toBind_1071_, lean_object* v___f_1072_, lean_object* v___f_1073_, lean_object* v_x1_1074_, lean_object* v_x2_1075_, uint8_t v_x3_1076_){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1077_ = lean_apply_1(v_p_1070_, v_x1_1074_);
lean_inc(v_toBind_1071_);
v___x_1078_ = lean_apply_4(v_toBind_1071_, lean_box(0), lean_box(0), v___x_1077_, v___f_1072_);
v___x_1079_ = lean_apply_4(v_toBind_1071_, lean_box(0), lean_box(0), v___x_1078_, v___f_1073_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__2___boxed(lean_object* v_p_1080_, lean_object* v_toBind_1081_, lean_object* v___f_1082_, lean_object* v___f_1083_, lean_object* v_x1_1084_, lean_object* v_x2_1085_, lean_object* v_x3_1086_){
_start:
{
uint8_t v_x3_225__boxed_1087_; lean_object* v_res_1088_; 
v_x3_225__boxed_1087_ = lean_unbox(v_x3_1086_);
v_res_1088_ = l_Std_IterM_anyM___redArg___lam__2(v_p_1080_, v_toBind_1081_, v___f_1082_, v___f_1083_, v_x1_1084_, v_x2_1085_, v_x3_225__boxed_1087_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg(lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v_p_1091_, lean_object* v_it_1092_){
_start:
{
lean_object* v_toApplicative_1093_; lean_object* v_toBind_1094_; lean_object* v_toPure_1095_; lean_object* v___f_1096_; lean_object* v___f_1097_; uint8_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___f_1100_; lean_object* v___f_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_toApplicative_1093_ = lean_ctor_get(v_inst_1089_, 0);
lean_inc_ref(v_toApplicative_1093_);
v_toBind_1094_ = lean_ctor_get(v_inst_1089_, 1);
lean_inc(v_toBind_1094_);
lean_dec_ref(v_inst_1089_);
v_toPure_1095_ = lean_ctor_get(v_toApplicative_1093_, 1);
lean_inc(v_toPure_1095_);
lean_dec_ref(v_toApplicative_1093_);
lean_inc(v_toBind_1094_);
v___f_1096_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1096_, 0, v_toBind_1094_);
lean_inc(v_toPure_1095_);
v___f_1097_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1097_, 0, v_toPure_1095_);
v___x_1098_ = 0;
v___x_1099_ = lean_box(v___x_1098_);
v___f_1100_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1100_, 0, v___x_1099_);
lean_closure_set(v___f_1100_, 1, v_toPure_1095_);
v___f_1101_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1101_, 0, v_p_1091_);
lean_closure_set(v___f_1101_, 1, v_toBind_1094_);
lean_closure_set(v___f_1101_, 2, v___f_1100_);
lean_closure_set(v___f_1101_, 3, v___f_1097_);
v___x_1102_ = lean_box(v___x_1098_);
v___x_1103_ = lean_apply_6(v_inst_1090_, v___f_1096_, lean_box(0), lean_box(0), v_it_1092_, v___x_1102_, v___f_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM(lean_object* v_00_u03b1_1104_, lean_object* v_00_u03b2_1105_, lean_object* v_m_1106_, lean_object* v_inst_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_p_1110_, lean_object* v_it_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Std_IterM_anyM___redArg(v_inst_1107_, v_inst_1109_, v_p_1110_, v_it_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___boxed(lean_object* v_00_u03b1_1113_, lean_object* v_00_u03b2_1114_, lean_object* v_m_1115_, lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_p_1119_, lean_object* v_it_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Std_IterM_anyM(v_00_u03b1_1113_, v_00_u03b2_1114_, v_m_1115_, v_inst_1116_, v_inst_1117_, v_inst_1118_, v_p_1119_, v_it_1120_);
lean_dec(v_inst_1117_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM___redArg(lean_object* v_inst_1122_, lean_object* v_inst_1123_, lean_object* v_p_1124_, lean_object* v_it_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Std_IterM_anyM___redArg(v_inst_1122_, v_inst_1123_, v_p_1124_, v_it_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM(lean_object* v_00_u03b1_1127_, lean_object* v_00_u03b2_1128_, lean_object* v_m_1129_, lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_p_1133_, lean_object* v_it_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Std_IterM_anyM___redArg(v_inst_1130_, v_inst_1132_, v_p_1133_, v_it_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM___boxed(lean_object* v_00_u03b1_1136_, lean_object* v_00_u03b2_1137_, lean_object* v_m_1138_, lean_object* v_inst_1139_, lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_p_1142_, lean_object* v_it_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Std_IterM_Partial_anyM(v_00_u03b1_1136_, v_00_u03b2_1137_, v_m_1138_, v_inst_1139_, v_inst_1140_, v_inst_1141_, v_p_1142_, v_it_1143_);
lean_dec(v_inst_1140_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM___redArg(lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_p_1147_, lean_object* v_it_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Std_IterM_anyM___redArg(v_inst_1145_, v_inst_1146_, v_p_1147_, v_it_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM(lean_object* v_00_u03b1_1150_, lean_object* v_00_u03b2_1151_, lean_object* v_m_1152_, lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_inst_1155_, lean_object* v_inst_1156_, lean_object* v_p_1157_, lean_object* v_it_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Std_IterM_anyM___redArg(v_inst_1153_, v_inst_1155_, v_p_1157_, v_it_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM___boxed(lean_object* v_00_u03b1_1160_, lean_object* v_00_u03b2_1161_, lean_object* v_m_1162_, lean_object* v_inst_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_p_1167_, lean_object* v_it_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Std_IterM_Total_anyM(v_00_u03b1_1160_, v_00_u03b2_1161_, v_m_1162_, v_inst_1163_, v_inst_1164_, v_inst_1165_, v_inst_1166_, v_p_1167_, v_it_1168_);
lean_dec(v_inst_1164_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any___redArg___lam__0(lean_object* v_p_1170_, lean_object* v_toPure_1171_, lean_object* v_x_1172_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_apply_1(v_p_1170_, v_x_1172_);
v___x_1174_ = lean_apply_2(v_toPure_1171_, lean_box(0), v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any___redArg(lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_p_1177_, lean_object* v_it_1178_){
_start:
{
lean_object* v_toApplicative_1179_; lean_object* v_toPure_1180_; lean_object* v___f_1181_; lean_object* v___x_1182_; 
v_toApplicative_1179_ = lean_ctor_get(v_inst_1175_, 0);
v_toPure_1180_ = lean_ctor_get(v_toApplicative_1179_, 1);
lean_inc(v_toPure_1180_);
v___f_1181_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1181_, 0, v_p_1177_);
lean_closure_set(v___f_1181_, 1, v_toPure_1180_);
v___x_1182_ = l_Std_IterM_anyM___redArg(v_inst_1175_, v_inst_1176_, v___f_1181_, v_it_1178_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any(lean_object* v_00_u03b1_1183_, lean_object* v_00_u03b2_1184_, lean_object* v_m_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_p_1189_, lean_object* v_it_1190_){
_start:
{
lean_object* v_toApplicative_1191_; lean_object* v_toPure_1192_; lean_object* v___f_1193_; lean_object* v___x_1194_; 
v_toApplicative_1191_ = lean_ctor_get(v_inst_1186_, 0);
v_toPure_1192_ = lean_ctor_get(v_toApplicative_1191_, 1);
lean_inc(v_toPure_1192_);
v___f_1193_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1193_, 0, v_p_1189_);
lean_closure_set(v___f_1193_, 1, v_toPure_1192_);
v___x_1194_ = l_Std_IterM_anyM___redArg(v_inst_1186_, v_inst_1188_, v___f_1193_, v_it_1190_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any___boxed(lean_object* v_00_u03b1_1195_, lean_object* v_00_u03b2_1196_, lean_object* v_m_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_inst_1200_, lean_object* v_p_1201_, lean_object* v_it_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Std_IterM_any(v_00_u03b1_1195_, v_00_u03b2_1196_, v_m_1197_, v_inst_1198_, v_inst_1199_, v_inst_1200_, v_p_1201_, v_it_1202_);
lean_dec(v_inst_1199_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any___redArg(lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_p_1206_, lean_object* v_it_1207_){
_start:
{
lean_object* v_toApplicative_1208_; lean_object* v_toPure_1209_; lean_object* v___f_1210_; lean_object* v___x_1211_; 
v_toApplicative_1208_ = lean_ctor_get(v_inst_1204_, 0);
v_toPure_1209_ = lean_ctor_get(v_toApplicative_1208_, 1);
lean_inc(v_toPure_1209_);
v___f_1210_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1210_, 0, v_p_1206_);
lean_closure_set(v___f_1210_, 1, v_toPure_1209_);
v___x_1211_ = l_Std_IterM_anyM___redArg(v_inst_1204_, v_inst_1205_, v___f_1210_, v_it_1207_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any(lean_object* v_00_u03b1_1212_, lean_object* v_00_u03b2_1213_, lean_object* v_m_1214_, lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_p_1218_, lean_object* v_it_1219_){
_start:
{
lean_object* v_toApplicative_1220_; lean_object* v_toPure_1221_; lean_object* v___f_1222_; lean_object* v___x_1223_; 
v_toApplicative_1220_ = lean_ctor_get(v_inst_1215_, 0);
v_toPure_1221_ = lean_ctor_get(v_toApplicative_1220_, 1);
lean_inc(v_toPure_1221_);
v___f_1222_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1222_, 0, v_p_1218_);
lean_closure_set(v___f_1222_, 1, v_toPure_1221_);
v___x_1223_ = l_Std_IterM_anyM___redArg(v_inst_1215_, v_inst_1217_, v___f_1222_, v_it_1219_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any___boxed(lean_object* v_00_u03b1_1224_, lean_object* v_00_u03b2_1225_, lean_object* v_m_1226_, lean_object* v_inst_1227_, lean_object* v_inst_1228_, lean_object* v_inst_1229_, lean_object* v_p_1230_, lean_object* v_it_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Std_IterM_Partial_any(v_00_u03b1_1224_, v_00_u03b2_1225_, v_m_1226_, v_inst_1227_, v_inst_1228_, v_inst_1229_, v_p_1230_, v_it_1231_);
lean_dec(v_inst_1228_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_any___redArg(lean_object* v_inst_1233_, lean_object* v_inst_1234_, lean_object* v_p_1235_, lean_object* v_it_1236_){
_start:
{
lean_object* v_toApplicative_1237_; lean_object* v_toPure_1238_; lean_object* v___f_1239_; lean_object* v___x_1240_; 
v_toApplicative_1237_ = lean_ctor_get(v_inst_1233_, 0);
v_toPure_1238_ = lean_ctor_get(v_toApplicative_1237_, 1);
lean_inc(v_toPure_1238_);
v___f_1239_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1239_, 0, v_p_1235_);
lean_closure_set(v___f_1239_, 1, v_toPure_1238_);
v___x_1240_ = l_Std_IterM_anyM___redArg(v_inst_1233_, v_inst_1234_, v___f_1239_, v_it_1236_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_any(lean_object* v_00_u03b1_1241_, lean_object* v_00_u03b2_1242_, lean_object* v_m_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_, lean_object* v_inst_1246_, lean_object* v_inst_1247_, lean_object* v_p_1248_, lean_object* v_it_1249_){
_start:
{
lean_object* v_toApplicative_1250_; lean_object* v_toPure_1251_; lean_object* v___f_1252_; lean_object* v___x_1253_; 
v_toApplicative_1250_ = lean_ctor_get(v_inst_1244_, 0);
v_toPure_1251_ = lean_ctor_get(v_toApplicative_1250_, 1);
lean_inc(v_toPure_1251_);
v___f_1252_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1252_, 0, v_p_1248_);
lean_closure_set(v___f_1252_, 1, v_toPure_1251_);
v___x_1253_ = l_Std_IterM_anyM___redArg(v_inst_1244_, v_inst_1246_, v___f_1252_, v_it_1249_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_any___boxed(lean_object* v_00_u03b1_1254_, lean_object* v_00_u03b2_1255_, lean_object* v_m_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_p_1261_, lean_object* v_it_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Std_IterM_Total_any(v_00_u03b1_1254_, v_00_u03b2_1255_, v_m_1256_, v_inst_1257_, v_inst_1258_, v_inst_1259_, v_inst_1260_, v_p_1261_, v_it_1262_);
lean_dec(v_inst_1258_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg___lam__2(lean_object* v_toPure_1264_, uint8_t v___x_1265_, uint8_t v_____do__lift_1266_){
_start:
{
if (v_____do__lift_1266_ == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = lean_box(v_____do__lift_1266_);
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
v___x_1269_ = lean_apply_2(v_toPure_1264_, lean_box(0), v___x_1268_);
return v___x_1269_;
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_box(v___x_1265_);
v___x_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
v___x_1272_ = lean_apply_2(v_toPure_1264_, lean_box(0), v___x_1271_);
return v___x_1272_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg___lam__2___boxed(lean_object* v_toPure_1273_, lean_object* v___x_1274_, lean_object* v_____do__lift_1275_){
_start:
{
uint8_t v___x_201__boxed_1276_; uint8_t v_____do__lift_202__boxed_1277_; lean_object* v_res_1278_; 
v___x_201__boxed_1276_ = lean_unbox(v___x_1274_);
v_____do__lift_202__boxed_1277_ = lean_unbox(v_____do__lift_1275_);
v_res_1278_ = l_Std_IterM_allM___redArg___lam__2(v_toPure_1273_, v___x_201__boxed_1276_, v_____do__lift_202__boxed_1277_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg(lean_object* v_inst_1279_, lean_object* v_inst_1280_, lean_object* v_p_1281_, lean_object* v_it_1282_){
_start:
{
lean_object* v_toApplicative_1283_; lean_object* v_toBind_1284_; lean_object* v_toPure_1285_; lean_object* v___f_1286_; lean_object* v___f_1287_; uint8_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___f_1290_; lean_object* v___f_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v_toApplicative_1283_ = lean_ctor_get(v_inst_1279_, 0);
lean_inc_ref(v_toApplicative_1283_);
v_toBind_1284_ = lean_ctor_get(v_inst_1279_, 1);
lean_inc(v_toBind_1284_);
lean_dec_ref(v_inst_1279_);
v_toPure_1285_ = lean_ctor_get(v_toApplicative_1283_, 1);
lean_inc(v_toPure_1285_);
lean_dec_ref(v_toApplicative_1283_);
lean_inc(v_toBind_1284_);
v___f_1286_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1286_, 0, v_toBind_1284_);
lean_inc(v_toPure_1285_);
v___f_1287_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1287_, 0, v_toPure_1285_);
v___x_1288_ = 1;
v___x_1289_ = lean_box(v___x_1288_);
v___f_1290_ = lean_alloc_closure((void*)(l_Std_IterM_allM___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1290_, 0, v_toPure_1285_);
lean_closure_set(v___f_1290_, 1, v___x_1289_);
v___f_1291_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1291_, 0, v_p_1281_);
lean_closure_set(v___f_1291_, 1, v_toBind_1284_);
lean_closure_set(v___f_1291_, 2, v___f_1290_);
lean_closure_set(v___f_1291_, 3, v___f_1287_);
v___x_1292_ = lean_box(v___x_1288_);
v___x_1293_ = lean_apply_6(v_inst_1280_, v___f_1286_, lean_box(0), lean_box(0), v_it_1282_, v___x_1292_, v___f_1291_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM(lean_object* v_00_u03b1_1294_, lean_object* v_00_u03b2_1295_, lean_object* v_m_1296_, lean_object* v_inst_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_p_1300_, lean_object* v_it_1301_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Std_IterM_allM___redArg(v_inst_1297_, v_inst_1299_, v_p_1300_, v_it_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM___boxed(lean_object* v_00_u03b1_1303_, lean_object* v_00_u03b2_1304_, lean_object* v_m_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_inst_1308_, lean_object* v_p_1309_, lean_object* v_it_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Std_IterM_allM(v_00_u03b1_1303_, v_00_u03b2_1304_, v_m_1305_, v_inst_1306_, v_inst_1307_, v_inst_1308_, v_p_1309_, v_it_1310_);
lean_dec(v_inst_1307_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM___redArg(lean_object* v_inst_1312_, lean_object* v_inst_1313_, lean_object* v_p_1314_, lean_object* v_it_1315_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Std_IterM_allM___redArg(v_inst_1312_, v_inst_1313_, v_p_1314_, v_it_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM(lean_object* v_00_u03b1_1317_, lean_object* v_00_u03b2_1318_, lean_object* v_m_1319_, lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_p_1323_, lean_object* v_it_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Std_IterM_allM___redArg(v_inst_1320_, v_inst_1322_, v_p_1323_, v_it_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM___boxed(lean_object* v_00_u03b1_1326_, lean_object* v_00_u03b2_1327_, lean_object* v_m_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_inst_1331_, lean_object* v_p_1332_, lean_object* v_it_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Std_IterM_Partial_allM(v_00_u03b1_1326_, v_00_u03b2_1327_, v_m_1328_, v_inst_1329_, v_inst_1330_, v_inst_1331_, v_p_1332_, v_it_1333_);
lean_dec(v_inst_1330_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM___redArg(lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_p_1337_, lean_object* v_it_1338_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Std_IterM_allM___redArg(v_inst_1335_, v_inst_1336_, v_p_1337_, v_it_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM(lean_object* v_00_u03b1_1340_, lean_object* v_00_u03b2_1341_, lean_object* v_m_1342_, lean_object* v_inst_1343_, lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_p_1347_, lean_object* v_it_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Std_IterM_allM___redArg(v_inst_1343_, v_inst_1345_, v_p_1347_, v_it_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM___boxed(lean_object* v_00_u03b1_1350_, lean_object* v_00_u03b2_1351_, lean_object* v_m_1352_, lean_object* v_inst_1353_, lean_object* v_inst_1354_, lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_p_1357_, lean_object* v_it_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Std_IterM_Total_allM(v_00_u03b1_1350_, v_00_u03b2_1351_, v_m_1352_, v_inst_1353_, v_inst_1354_, v_inst_1355_, v_inst_1356_, v_p_1357_, v_it_1358_);
lean_dec(v_inst_1354_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_all___redArg(lean_object* v_inst_1360_, lean_object* v_inst_1361_, lean_object* v_p_1362_, lean_object* v_it_1363_){
_start:
{
lean_object* v_toApplicative_1364_; lean_object* v_toPure_1365_; lean_object* v___f_1366_; lean_object* v___x_1367_; 
v_toApplicative_1364_ = lean_ctor_get(v_inst_1360_, 0);
v_toPure_1365_ = lean_ctor_get(v_toApplicative_1364_, 1);
lean_inc(v_toPure_1365_);
v___f_1366_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1366_, 0, v_p_1362_);
lean_closure_set(v___f_1366_, 1, v_toPure_1365_);
v___x_1367_ = l_Std_IterM_allM___redArg(v_inst_1360_, v_inst_1361_, v___f_1366_, v_it_1363_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_all(lean_object* v_00_u03b1_1368_, lean_object* v_00_u03b2_1369_, lean_object* v_m_1370_, lean_object* v_inst_1371_, lean_object* v_inst_1372_, lean_object* v_inst_1373_, lean_object* v_p_1374_, lean_object* v_it_1375_){
_start:
{
lean_object* v_toApplicative_1376_; lean_object* v_toPure_1377_; lean_object* v___f_1378_; lean_object* v___x_1379_; 
v_toApplicative_1376_ = lean_ctor_get(v_inst_1371_, 0);
v_toPure_1377_ = lean_ctor_get(v_toApplicative_1376_, 1);
lean_inc(v_toPure_1377_);
v___f_1378_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1378_, 0, v_p_1374_);
lean_closure_set(v___f_1378_, 1, v_toPure_1377_);
v___x_1379_ = l_Std_IterM_allM___redArg(v_inst_1371_, v_inst_1373_, v___f_1378_, v_it_1375_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_all___boxed(lean_object* v_00_u03b1_1380_, lean_object* v_00_u03b2_1381_, lean_object* v_m_1382_, lean_object* v_inst_1383_, lean_object* v_inst_1384_, lean_object* v_inst_1385_, lean_object* v_p_1386_, lean_object* v_it_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Std_IterM_all(v_00_u03b1_1380_, v_00_u03b2_1381_, v_m_1382_, v_inst_1383_, v_inst_1384_, v_inst_1385_, v_p_1386_, v_it_1387_);
lean_dec(v_inst_1384_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all___redArg(lean_object* v_inst_1389_, lean_object* v_inst_1390_, lean_object* v_p_1391_, lean_object* v_it_1392_){
_start:
{
lean_object* v_toApplicative_1393_; lean_object* v_toPure_1394_; lean_object* v___f_1395_; lean_object* v___x_1396_; 
v_toApplicative_1393_ = lean_ctor_get(v_inst_1389_, 0);
v_toPure_1394_ = lean_ctor_get(v_toApplicative_1393_, 1);
lean_inc(v_toPure_1394_);
v___f_1395_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1395_, 0, v_p_1391_);
lean_closure_set(v___f_1395_, 1, v_toPure_1394_);
v___x_1396_ = l_Std_IterM_allM___redArg(v_inst_1389_, v_inst_1390_, v___f_1395_, v_it_1392_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all(lean_object* v_00_u03b1_1397_, lean_object* v_00_u03b2_1398_, lean_object* v_m_1399_, lean_object* v_inst_1400_, lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v_p_1403_, lean_object* v_it_1404_){
_start:
{
lean_object* v_toApplicative_1405_; lean_object* v_toPure_1406_; lean_object* v___f_1407_; lean_object* v___x_1408_; 
v_toApplicative_1405_ = lean_ctor_get(v_inst_1400_, 0);
v_toPure_1406_ = lean_ctor_get(v_toApplicative_1405_, 1);
lean_inc(v_toPure_1406_);
v___f_1407_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1407_, 0, v_p_1403_);
lean_closure_set(v___f_1407_, 1, v_toPure_1406_);
v___x_1408_ = l_Std_IterM_allM___redArg(v_inst_1400_, v_inst_1402_, v___f_1407_, v_it_1404_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all___boxed(lean_object* v_00_u03b1_1409_, lean_object* v_00_u03b2_1410_, lean_object* v_m_1411_, lean_object* v_inst_1412_, lean_object* v_inst_1413_, lean_object* v_inst_1414_, lean_object* v_p_1415_, lean_object* v_it_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Std_IterM_Partial_all(v_00_u03b1_1409_, v_00_u03b2_1410_, v_m_1411_, v_inst_1412_, v_inst_1413_, v_inst_1414_, v_p_1415_, v_it_1416_);
lean_dec(v_inst_1413_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_all___redArg(lean_object* v_inst_1418_, lean_object* v_inst_1419_, lean_object* v_p_1420_, lean_object* v_it_1421_){
_start:
{
lean_object* v_toApplicative_1422_; lean_object* v_toPure_1423_; lean_object* v___f_1424_; lean_object* v___x_1425_; 
v_toApplicative_1422_ = lean_ctor_get(v_inst_1418_, 0);
v_toPure_1423_ = lean_ctor_get(v_toApplicative_1422_, 1);
lean_inc(v_toPure_1423_);
v___f_1424_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1424_, 0, v_p_1420_);
lean_closure_set(v___f_1424_, 1, v_toPure_1423_);
v___x_1425_ = l_Std_IterM_allM___redArg(v_inst_1418_, v_inst_1419_, v___f_1424_, v_it_1421_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_all(lean_object* v_00_u03b1_1426_, lean_object* v_00_u03b2_1427_, lean_object* v_m_1428_, lean_object* v_inst_1429_, lean_object* v_inst_1430_, lean_object* v_inst_1431_, lean_object* v_inst_1432_, lean_object* v_p_1433_, lean_object* v_it_1434_){
_start:
{
lean_object* v_toApplicative_1435_; lean_object* v_toPure_1436_; lean_object* v___f_1437_; lean_object* v___x_1438_; 
v_toApplicative_1435_ = lean_ctor_get(v_inst_1429_, 0);
v_toPure_1436_ = lean_ctor_get(v_toApplicative_1435_, 1);
lean_inc(v_toPure_1436_);
v___f_1437_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1437_, 0, v_p_1433_);
lean_closure_set(v___f_1437_, 1, v_toPure_1436_);
v___x_1438_ = l_Std_IterM_allM___redArg(v_inst_1429_, v_inst_1431_, v___f_1437_, v_it_1434_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_all___boxed(lean_object* v_00_u03b1_1439_, lean_object* v_00_u03b2_1440_, lean_object* v_m_1441_, lean_object* v_inst_1442_, lean_object* v_inst_1443_, lean_object* v_inst_1444_, lean_object* v_inst_1445_, lean_object* v_p_1446_, lean_object* v_it_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Std_IterM_Total_all(v_00_u03b1_1439_, v_00_u03b2_1440_, v_m_1441_, v_inst_1442_, v_inst_1443_, v_inst_1444_, v_inst_1445_, v_p_1446_, v_it_1447_);
lean_dec(v_inst_1443_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__1(lean_object* v_toPure_1449_, lean_object* v_____do__lift_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_apply_2(v_toPure_1449_, lean_box(0), v_____do__lift_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__0(lean_object* v___x_1452_, lean_object* v_toPure_1453_, lean_object* v_____do__lift_1454_){
_start:
{
if (lean_obj_tag(v_____do__lift_1454_) == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1452_);
v___x_1456_ = lean_apply_2(v_toPure_1453_, lean_box(0), v___x_1455_);
return v___x_1456_;
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec(v___x_1452_);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v_____do__lift_1454_);
v___x_1458_ = lean_apply_2(v_toPure_1453_, lean_box(0), v___x_1457_);
return v___x_1458_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__2(lean_object* v_f_1459_, lean_object* v_toBind_1460_, lean_object* v___f_1461_, lean_object* v___f_1462_, lean_object* v_x1_1463_, lean_object* v_x2_1464_, lean_object* v_x3_1465_){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1466_ = lean_apply_1(v_f_1459_, v_x1_1463_);
lean_inc(v_toBind_1460_);
v___x_1467_ = lean_apply_4(v_toBind_1460_, lean_box(0), lean_box(0), v___x_1466_, v___f_1461_);
v___x_1468_ = lean_apply_4(v_toBind_1460_, lean_box(0), lean_box(0), v___x_1467_, v___f_1462_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed(lean_object* v_f_1469_, lean_object* v_toBind_1470_, lean_object* v___f_1471_, lean_object* v___f_1472_, lean_object* v_x1_1473_, lean_object* v_x2_1474_, lean_object* v_x3_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Std_IterM_findSomeM_x3f___redArg___lam__2(v_f_1469_, v_toBind_1470_, v___f_1471_, v___f_1472_, v_x1_1473_, v_x2_1474_, v_x3_1475_);
lean_dec(v_x3_1475_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg(lean_object* v_inst_1477_, lean_object* v_inst_1478_, lean_object* v_it_1479_, lean_object* v_f_1480_){
_start:
{
lean_object* v_toApplicative_1481_; lean_object* v_toBind_1482_; lean_object* v_toPure_1483_; lean_object* v___f_1484_; lean_object* v___f_1485_; lean_object* v___x_1486_; lean_object* v___f_1487_; lean_object* v___f_1488_; lean_object* v___x_1489_; 
v_toApplicative_1481_ = lean_ctor_get(v_inst_1477_, 0);
lean_inc_ref(v_toApplicative_1481_);
v_toBind_1482_ = lean_ctor_get(v_inst_1477_, 1);
lean_inc(v_toBind_1482_);
lean_dec_ref(v_inst_1477_);
v_toPure_1483_ = lean_ctor_get(v_toApplicative_1481_, 1);
lean_inc(v_toPure_1483_);
lean_dec_ref(v_toApplicative_1481_);
lean_inc(v_toBind_1482_);
v___f_1484_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1484_, 0, v_toBind_1482_);
lean_inc(v_toPure_1483_);
v___f_1485_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1485_, 0, v_toPure_1483_);
v___x_1486_ = lean_box(0);
v___f_1487_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1487_, 0, v___x_1486_);
lean_closure_set(v___f_1487_, 1, v_toPure_1483_);
v___f_1488_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1488_, 0, v_f_1480_);
lean_closure_set(v___f_1488_, 1, v_toBind_1482_);
lean_closure_set(v___f_1488_, 2, v___f_1487_);
lean_closure_set(v___f_1488_, 3, v___f_1485_);
v___x_1489_ = lean_apply_6(v_inst_1478_, v___f_1484_, lean_box(0), lean_box(0), v_it_1479_, v___x_1486_, v___f_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f(lean_object* v_00_u03b1_1490_, lean_object* v_00_u03b2_1491_, lean_object* v_00_u03b3_1492_, lean_object* v_m_1493_, lean_object* v_inst_1494_, lean_object* v_inst_1495_, lean_object* v_inst_1496_, lean_object* v_it_1497_, lean_object* v_f_1498_){
_start:
{
lean_object* v_toApplicative_1499_; lean_object* v_toBind_1500_; lean_object* v_toPure_1501_; lean_object* v___f_1502_; lean_object* v___f_1503_; lean_object* v___x_1504_; lean_object* v___f_1505_; lean_object* v___f_1506_; lean_object* v___x_1507_; 
v_toApplicative_1499_ = lean_ctor_get(v_inst_1494_, 0);
lean_inc_ref(v_toApplicative_1499_);
v_toBind_1500_ = lean_ctor_get(v_inst_1494_, 1);
lean_inc(v_toBind_1500_);
lean_dec_ref(v_inst_1494_);
v_toPure_1501_ = lean_ctor_get(v_toApplicative_1499_, 1);
lean_inc(v_toPure_1501_);
lean_dec_ref(v_toApplicative_1499_);
lean_inc(v_toBind_1500_);
v___f_1502_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1502_, 0, v_toBind_1500_);
lean_inc(v_toPure_1501_);
v___f_1503_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1503_, 0, v_toPure_1501_);
v___x_1504_ = lean_box(0);
v___f_1505_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1505_, 0, v___x_1504_);
lean_closure_set(v___f_1505_, 1, v_toPure_1501_);
v___f_1506_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1506_, 0, v_f_1498_);
lean_closure_set(v___f_1506_, 1, v_toBind_1500_);
lean_closure_set(v___f_1506_, 2, v___f_1505_);
lean_closure_set(v___f_1506_, 3, v___f_1503_);
v___x_1507_ = lean_apply_6(v_inst_1496_, v___f_1502_, lean_box(0), lean_box(0), v_it_1497_, v___x_1504_, v___f_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___boxed(lean_object* v_00_u03b1_1508_, lean_object* v_00_u03b2_1509_, lean_object* v_00_u03b3_1510_, lean_object* v_m_1511_, lean_object* v_inst_1512_, lean_object* v_inst_1513_, lean_object* v_inst_1514_, lean_object* v_it_1515_, lean_object* v_f_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Std_IterM_findSomeM_x3f(v_00_u03b1_1508_, v_00_u03b2_1509_, v_00_u03b3_1510_, v_m_1511_, v_inst_1512_, v_inst_1513_, v_inst_1514_, v_it_1515_, v_f_1516_);
lean_dec(v_inst_1513_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f___redArg(lean_object* v_inst_1518_, lean_object* v_inst_1519_, lean_object* v_it_1520_, lean_object* v_f_1521_){
_start:
{
lean_object* v_toApplicative_1522_; lean_object* v_toBind_1523_; lean_object* v_toPure_1524_; lean_object* v___f_1525_; lean_object* v___f_1526_; lean_object* v___x_1527_; lean_object* v___f_1528_; lean_object* v___f_1529_; lean_object* v___x_1530_; 
v_toApplicative_1522_ = lean_ctor_get(v_inst_1518_, 0);
lean_inc_ref(v_toApplicative_1522_);
v_toBind_1523_ = lean_ctor_get(v_inst_1518_, 1);
lean_inc(v_toBind_1523_);
lean_dec_ref(v_inst_1518_);
v_toPure_1524_ = lean_ctor_get(v_toApplicative_1522_, 1);
lean_inc(v_toPure_1524_);
lean_dec_ref(v_toApplicative_1522_);
lean_inc(v_toBind_1523_);
v___f_1525_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1525_, 0, v_toBind_1523_);
lean_inc(v_toPure_1524_);
v___f_1526_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1526_, 0, v_toPure_1524_);
v___x_1527_ = lean_box(0);
v___f_1528_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1528_, 0, v___x_1527_);
lean_closure_set(v___f_1528_, 1, v_toPure_1524_);
v___f_1529_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1529_, 0, v_f_1521_);
lean_closure_set(v___f_1529_, 1, v_toBind_1523_);
lean_closure_set(v___f_1529_, 2, v___f_1528_);
lean_closure_set(v___f_1529_, 3, v___f_1526_);
v___x_1530_ = lean_apply_6(v_inst_1519_, v___f_1525_, lean_box(0), lean_box(0), v_it_1520_, v___x_1527_, v___f_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f(lean_object* v_00_u03b1_1531_, lean_object* v_00_u03b2_1532_, lean_object* v_00_u03b3_1533_, lean_object* v_m_1534_, lean_object* v_inst_1535_, lean_object* v_inst_1536_, lean_object* v_inst_1537_, lean_object* v_it_1538_, lean_object* v_f_1539_){
_start:
{
lean_object* v_toApplicative_1540_; lean_object* v_toBind_1541_; lean_object* v_toPure_1542_; lean_object* v___f_1543_; lean_object* v___f_1544_; lean_object* v___x_1545_; lean_object* v___f_1546_; lean_object* v___f_1547_; lean_object* v___x_1548_; 
v_toApplicative_1540_ = lean_ctor_get(v_inst_1535_, 0);
lean_inc_ref(v_toApplicative_1540_);
v_toBind_1541_ = lean_ctor_get(v_inst_1535_, 1);
lean_inc(v_toBind_1541_);
lean_dec_ref(v_inst_1535_);
v_toPure_1542_ = lean_ctor_get(v_toApplicative_1540_, 1);
lean_inc(v_toPure_1542_);
lean_dec_ref(v_toApplicative_1540_);
lean_inc(v_toBind_1541_);
v___f_1543_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1543_, 0, v_toBind_1541_);
lean_inc(v_toPure_1542_);
v___f_1544_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1544_, 0, v_toPure_1542_);
v___x_1545_ = lean_box(0);
v___f_1546_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1546_, 0, v___x_1545_);
lean_closure_set(v___f_1546_, 1, v_toPure_1542_);
v___f_1547_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1547_, 0, v_f_1539_);
lean_closure_set(v___f_1547_, 1, v_toBind_1541_);
lean_closure_set(v___f_1547_, 2, v___f_1546_);
lean_closure_set(v___f_1547_, 3, v___f_1544_);
v___x_1548_ = lean_apply_6(v_inst_1537_, v___f_1543_, lean_box(0), lean_box(0), v_it_1538_, v___x_1545_, v___f_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f___boxed(lean_object* v_00_u03b1_1549_, lean_object* v_00_u03b2_1550_, lean_object* v_00_u03b3_1551_, lean_object* v_m_1552_, lean_object* v_inst_1553_, lean_object* v_inst_1554_, lean_object* v_inst_1555_, lean_object* v_it_1556_, lean_object* v_f_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Std_IterM_Partial_findSomeM_x3f(v_00_u03b1_1549_, v_00_u03b2_1550_, v_00_u03b3_1551_, v_m_1552_, v_inst_1553_, v_inst_1554_, v_inst_1555_, v_it_1556_, v_f_1557_);
lean_dec(v_inst_1554_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f___redArg(lean_object* v_inst_1559_, lean_object* v_inst_1560_, lean_object* v_it_1561_, lean_object* v_f_1562_){
_start:
{
lean_object* v_toApplicative_1563_; lean_object* v_toBind_1564_; lean_object* v_toPure_1565_; lean_object* v___f_1566_; lean_object* v___f_1567_; lean_object* v___x_1568_; lean_object* v___f_1569_; lean_object* v___f_1570_; lean_object* v___x_1571_; 
v_toApplicative_1563_ = lean_ctor_get(v_inst_1559_, 0);
lean_inc_ref(v_toApplicative_1563_);
v_toBind_1564_ = lean_ctor_get(v_inst_1559_, 1);
lean_inc(v_toBind_1564_);
lean_dec_ref(v_inst_1559_);
v_toPure_1565_ = lean_ctor_get(v_toApplicative_1563_, 1);
lean_inc(v_toPure_1565_);
lean_dec_ref(v_toApplicative_1563_);
lean_inc(v_toBind_1564_);
v___f_1566_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1566_, 0, v_toBind_1564_);
lean_inc(v_toPure_1565_);
v___f_1567_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1567_, 0, v_toPure_1565_);
v___x_1568_ = lean_box(0);
v___f_1569_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1569_, 0, v___x_1568_);
lean_closure_set(v___f_1569_, 1, v_toPure_1565_);
v___f_1570_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1570_, 0, v_f_1562_);
lean_closure_set(v___f_1570_, 1, v_toBind_1564_);
lean_closure_set(v___f_1570_, 2, v___f_1569_);
lean_closure_set(v___f_1570_, 3, v___f_1567_);
v___x_1571_ = lean_apply_6(v_inst_1560_, v___f_1566_, lean_box(0), lean_box(0), v_it_1561_, v___x_1568_, v___f_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f(lean_object* v_00_u03b1_1572_, lean_object* v_00_u03b2_1573_, lean_object* v_00_u03b3_1574_, lean_object* v_m_1575_, lean_object* v_inst_1576_, lean_object* v_inst_1577_, lean_object* v_inst_1578_, lean_object* v_inst_1579_, lean_object* v_it_1580_, lean_object* v_f_1581_){
_start:
{
lean_object* v_toApplicative_1582_; lean_object* v_toBind_1583_; lean_object* v_toPure_1584_; lean_object* v___f_1585_; lean_object* v___f_1586_; lean_object* v___x_1587_; lean_object* v___f_1588_; lean_object* v___f_1589_; lean_object* v___x_1590_; 
v_toApplicative_1582_ = lean_ctor_get(v_inst_1576_, 0);
lean_inc_ref(v_toApplicative_1582_);
v_toBind_1583_ = lean_ctor_get(v_inst_1576_, 1);
lean_inc(v_toBind_1583_);
lean_dec_ref(v_inst_1576_);
v_toPure_1584_ = lean_ctor_get(v_toApplicative_1582_, 1);
lean_inc(v_toPure_1584_);
lean_dec_ref(v_toApplicative_1582_);
lean_inc(v_toBind_1583_);
v___f_1585_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1585_, 0, v_toBind_1583_);
lean_inc(v_toPure_1584_);
v___f_1586_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1586_, 0, v_toPure_1584_);
v___x_1587_ = lean_box(0);
v___f_1588_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1588_, 0, v___x_1587_);
lean_closure_set(v___f_1588_, 1, v_toPure_1584_);
v___f_1589_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1589_, 0, v_f_1581_);
lean_closure_set(v___f_1589_, 1, v_toBind_1583_);
lean_closure_set(v___f_1589_, 2, v___f_1588_);
lean_closure_set(v___f_1589_, 3, v___f_1586_);
v___x_1590_ = lean_apply_6(v_inst_1578_, v___f_1585_, lean_box(0), lean_box(0), v_it_1580_, v___x_1587_, v___f_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f___boxed(lean_object* v_00_u03b1_1591_, lean_object* v_00_u03b2_1592_, lean_object* v_00_u03b3_1593_, lean_object* v_m_1594_, lean_object* v_inst_1595_, lean_object* v_inst_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_it_1599_, lean_object* v_f_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Std_IterM_Total_findSomeM_x3f(v_00_u03b1_1591_, v_00_u03b2_1592_, v_00_u03b3_1593_, v_m_1594_, v_inst_1595_, v_inst_1596_, v_inst_1597_, v_inst_1598_, v_it_1599_, v_f_1600_);
lean_dec(v_inst_1596_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg___lam__3(lean_object* v_f_1602_, lean_object* v_toPure_1603_, lean_object* v_toBind_1604_, lean_object* v___f_1605_, lean_object* v___f_1606_, lean_object* v_x1_1607_, lean_object* v_x2_1608_, lean_object* v_x3_1609_){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1610_ = lean_apply_1(v_f_1602_, v_x1_1607_);
v___x_1611_ = lean_apply_2(v_toPure_1603_, lean_box(0), v___x_1610_);
lean_inc(v_toBind_1604_);
v___x_1612_ = lean_apply_4(v_toBind_1604_, lean_box(0), lean_box(0), v___x_1611_, v___f_1605_);
v___x_1613_ = lean_apply_4(v_toBind_1604_, lean_box(0), lean_box(0), v___x_1612_, v___f_1606_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg___lam__3___boxed(lean_object* v_f_1614_, lean_object* v_toPure_1615_, lean_object* v_toBind_1616_, lean_object* v___f_1617_, lean_object* v___f_1618_, lean_object* v_x1_1619_, lean_object* v_x2_1620_, lean_object* v_x3_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Std_IterM_findSome_x3f___redArg___lam__3(v_f_1614_, v_toPure_1615_, v_toBind_1616_, v___f_1617_, v___f_1618_, v_x1_1619_, v_x2_1620_, v_x3_1621_);
lean_dec(v_x3_1621_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg(lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_it_1625_, lean_object* v_f_1626_){
_start:
{
lean_object* v_toApplicative_1627_; lean_object* v_toBind_1628_; lean_object* v_toPure_1629_; lean_object* v___f_1630_; lean_object* v___f_1631_; lean_object* v___x_1632_; lean_object* v___f_1633_; lean_object* v___f_1634_; lean_object* v___x_1635_; 
v_toApplicative_1627_ = lean_ctor_get(v_inst_1623_, 0);
lean_inc_ref(v_toApplicative_1627_);
v_toBind_1628_ = lean_ctor_get(v_inst_1623_, 1);
lean_inc(v_toBind_1628_);
lean_dec_ref(v_inst_1623_);
v_toPure_1629_ = lean_ctor_get(v_toApplicative_1627_, 1);
lean_inc(v_toPure_1629_);
lean_dec_ref(v_toApplicative_1627_);
lean_inc(v_toBind_1628_);
v___f_1630_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1630_, 0, v_toBind_1628_);
lean_inc(v_toPure_1629_);
v___f_1631_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1631_, 0, v_toPure_1629_);
v___x_1632_ = lean_box(0);
lean_inc(v_toPure_1629_);
v___f_1633_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1633_, 0, v___x_1632_);
lean_closure_set(v___f_1633_, 1, v_toPure_1629_);
v___f_1634_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1634_, 0, v_f_1626_);
lean_closure_set(v___f_1634_, 1, v_toPure_1629_);
lean_closure_set(v___f_1634_, 2, v_toBind_1628_);
lean_closure_set(v___f_1634_, 3, v___f_1633_);
lean_closure_set(v___f_1634_, 4, v___f_1631_);
v___x_1635_ = lean_apply_6(v_inst_1624_, v___f_1630_, lean_box(0), lean_box(0), v_it_1625_, v___x_1632_, v___f_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f(lean_object* v_00_u03b1_1636_, lean_object* v_00_u03b2_1637_, lean_object* v_00_u03b3_1638_, lean_object* v_m_1639_, lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_it_1643_, lean_object* v_f_1644_){
_start:
{
lean_object* v_toApplicative_1645_; lean_object* v_toBind_1646_; lean_object* v_toPure_1647_; lean_object* v___f_1648_; lean_object* v___f_1649_; lean_object* v___x_1650_; lean_object* v___f_1651_; lean_object* v___f_1652_; lean_object* v___x_1653_; 
v_toApplicative_1645_ = lean_ctor_get(v_inst_1640_, 0);
lean_inc_ref(v_toApplicative_1645_);
v_toBind_1646_ = lean_ctor_get(v_inst_1640_, 1);
lean_inc(v_toBind_1646_);
lean_dec_ref(v_inst_1640_);
v_toPure_1647_ = lean_ctor_get(v_toApplicative_1645_, 1);
lean_inc(v_toPure_1647_);
lean_dec_ref(v_toApplicative_1645_);
lean_inc(v_toBind_1646_);
v___f_1648_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1648_, 0, v_toBind_1646_);
lean_inc(v_toPure_1647_);
v___f_1649_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1649_, 0, v_toPure_1647_);
v___x_1650_ = lean_box(0);
lean_inc(v_toPure_1647_);
v___f_1651_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1651_, 0, v___x_1650_);
lean_closure_set(v___f_1651_, 1, v_toPure_1647_);
v___f_1652_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1652_, 0, v_f_1644_);
lean_closure_set(v___f_1652_, 1, v_toPure_1647_);
lean_closure_set(v___f_1652_, 2, v_toBind_1646_);
lean_closure_set(v___f_1652_, 3, v___f_1651_);
lean_closure_set(v___f_1652_, 4, v___f_1649_);
v___x_1653_ = lean_apply_6(v_inst_1642_, v___f_1648_, lean_box(0), lean_box(0), v_it_1643_, v___x_1650_, v___f_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___boxed(lean_object* v_00_u03b1_1654_, lean_object* v_00_u03b2_1655_, lean_object* v_00_u03b3_1656_, lean_object* v_m_1657_, lean_object* v_inst_1658_, lean_object* v_inst_1659_, lean_object* v_inst_1660_, lean_object* v_it_1661_, lean_object* v_f_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Std_IterM_findSome_x3f(v_00_u03b1_1654_, v_00_u03b2_1655_, v_00_u03b3_1656_, v_m_1657_, v_inst_1658_, v_inst_1659_, v_inst_1660_, v_it_1661_, v_f_1662_);
lean_dec(v_inst_1659_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f___redArg(lean_object* v_inst_1664_, lean_object* v_inst_1665_, lean_object* v_it_1666_, lean_object* v_f_1667_){
_start:
{
lean_object* v_toApplicative_1668_; lean_object* v_toBind_1669_; lean_object* v_toPure_1670_; lean_object* v___f_1671_; lean_object* v___f_1672_; lean_object* v___x_1673_; lean_object* v___f_1674_; lean_object* v___f_1675_; lean_object* v___x_1676_; 
v_toApplicative_1668_ = lean_ctor_get(v_inst_1664_, 0);
lean_inc_ref(v_toApplicative_1668_);
v_toBind_1669_ = lean_ctor_get(v_inst_1664_, 1);
lean_inc(v_toBind_1669_);
lean_dec_ref(v_inst_1664_);
v_toPure_1670_ = lean_ctor_get(v_toApplicative_1668_, 1);
lean_inc(v_toPure_1670_);
lean_dec_ref(v_toApplicative_1668_);
lean_inc(v_toBind_1669_);
v___f_1671_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1671_, 0, v_toBind_1669_);
lean_inc(v_toPure_1670_);
v___f_1672_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1672_, 0, v_toPure_1670_);
v___x_1673_ = lean_box(0);
lean_inc(v_toPure_1670_);
v___f_1674_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1674_, 0, v___x_1673_);
lean_closure_set(v___f_1674_, 1, v_toPure_1670_);
v___f_1675_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1675_, 0, v_f_1667_);
lean_closure_set(v___f_1675_, 1, v_toPure_1670_);
lean_closure_set(v___f_1675_, 2, v_toBind_1669_);
lean_closure_set(v___f_1675_, 3, v___f_1674_);
lean_closure_set(v___f_1675_, 4, v___f_1672_);
v___x_1676_ = lean_apply_6(v_inst_1665_, v___f_1671_, lean_box(0), lean_box(0), v_it_1666_, v___x_1673_, v___f_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f(lean_object* v_00_u03b1_1677_, lean_object* v_00_u03b2_1678_, lean_object* v_00_u03b3_1679_, lean_object* v_m_1680_, lean_object* v_inst_1681_, lean_object* v_inst_1682_, lean_object* v_inst_1683_, lean_object* v_it_1684_, lean_object* v_f_1685_){
_start:
{
lean_object* v_toApplicative_1686_; lean_object* v_toBind_1687_; lean_object* v_toPure_1688_; lean_object* v___f_1689_; lean_object* v___f_1690_; lean_object* v___x_1691_; lean_object* v___f_1692_; lean_object* v___f_1693_; lean_object* v___x_1694_; 
v_toApplicative_1686_ = lean_ctor_get(v_inst_1681_, 0);
lean_inc_ref(v_toApplicative_1686_);
v_toBind_1687_ = lean_ctor_get(v_inst_1681_, 1);
lean_inc(v_toBind_1687_);
lean_dec_ref(v_inst_1681_);
v_toPure_1688_ = lean_ctor_get(v_toApplicative_1686_, 1);
lean_inc(v_toPure_1688_);
lean_dec_ref(v_toApplicative_1686_);
lean_inc(v_toBind_1687_);
v___f_1689_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1689_, 0, v_toBind_1687_);
lean_inc(v_toPure_1688_);
v___f_1690_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1690_, 0, v_toPure_1688_);
v___x_1691_ = lean_box(0);
lean_inc(v_toPure_1688_);
v___f_1692_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1692_, 0, v___x_1691_);
lean_closure_set(v___f_1692_, 1, v_toPure_1688_);
v___f_1693_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1693_, 0, v_f_1685_);
lean_closure_set(v___f_1693_, 1, v_toPure_1688_);
lean_closure_set(v___f_1693_, 2, v_toBind_1687_);
lean_closure_set(v___f_1693_, 3, v___f_1692_);
lean_closure_set(v___f_1693_, 4, v___f_1690_);
v___x_1694_ = lean_apply_6(v_inst_1683_, v___f_1689_, lean_box(0), lean_box(0), v_it_1684_, v___x_1691_, v___f_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f___boxed(lean_object* v_00_u03b1_1695_, lean_object* v_00_u03b2_1696_, lean_object* v_00_u03b3_1697_, lean_object* v_m_1698_, lean_object* v_inst_1699_, lean_object* v_inst_1700_, lean_object* v_inst_1701_, lean_object* v_it_1702_, lean_object* v_f_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Std_IterM_Partial_findSome_x3f(v_00_u03b1_1695_, v_00_u03b2_1696_, v_00_u03b3_1697_, v_m_1698_, v_inst_1699_, v_inst_1700_, v_inst_1701_, v_it_1702_, v_f_1703_);
lean_dec(v_inst_1700_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f___redArg(lean_object* v_inst_1705_, lean_object* v_inst_1706_, lean_object* v_it_1707_, lean_object* v_f_1708_){
_start:
{
lean_object* v_toApplicative_1709_; lean_object* v_toBind_1710_; lean_object* v_toPure_1711_; lean_object* v___f_1712_; lean_object* v___f_1713_; lean_object* v___x_1714_; lean_object* v___f_1715_; lean_object* v___f_1716_; lean_object* v___x_1717_; 
v_toApplicative_1709_ = lean_ctor_get(v_inst_1705_, 0);
lean_inc_ref(v_toApplicative_1709_);
v_toBind_1710_ = lean_ctor_get(v_inst_1705_, 1);
lean_inc(v_toBind_1710_);
lean_dec_ref(v_inst_1705_);
v_toPure_1711_ = lean_ctor_get(v_toApplicative_1709_, 1);
lean_inc(v_toPure_1711_);
lean_dec_ref(v_toApplicative_1709_);
lean_inc(v_toBind_1710_);
v___f_1712_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1712_, 0, v_toBind_1710_);
lean_inc(v_toPure_1711_);
v___f_1713_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1713_, 0, v_toPure_1711_);
v___x_1714_ = lean_box(0);
lean_inc(v_toPure_1711_);
v___f_1715_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1715_, 0, v___x_1714_);
lean_closure_set(v___f_1715_, 1, v_toPure_1711_);
v___f_1716_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1716_, 0, v_f_1708_);
lean_closure_set(v___f_1716_, 1, v_toPure_1711_);
lean_closure_set(v___f_1716_, 2, v_toBind_1710_);
lean_closure_set(v___f_1716_, 3, v___f_1715_);
lean_closure_set(v___f_1716_, 4, v___f_1713_);
v___x_1717_ = lean_apply_6(v_inst_1706_, v___f_1712_, lean_box(0), lean_box(0), v_it_1707_, v___x_1714_, v___f_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f(lean_object* v_00_u03b1_1718_, lean_object* v_00_u03b2_1719_, lean_object* v_00_u03b3_1720_, lean_object* v_m_1721_, lean_object* v_inst_1722_, lean_object* v_inst_1723_, lean_object* v_inst_1724_, lean_object* v_inst_1725_, lean_object* v_it_1726_, lean_object* v_f_1727_){
_start:
{
lean_object* v_toApplicative_1728_; lean_object* v_toBind_1729_; lean_object* v_toPure_1730_; lean_object* v___f_1731_; lean_object* v___f_1732_; lean_object* v___x_1733_; lean_object* v___f_1734_; lean_object* v___f_1735_; lean_object* v___x_1736_; 
v_toApplicative_1728_ = lean_ctor_get(v_inst_1722_, 0);
lean_inc_ref(v_toApplicative_1728_);
v_toBind_1729_ = lean_ctor_get(v_inst_1722_, 1);
lean_inc(v_toBind_1729_);
lean_dec_ref(v_inst_1722_);
v_toPure_1730_ = lean_ctor_get(v_toApplicative_1728_, 1);
lean_inc(v_toPure_1730_);
lean_dec_ref(v_toApplicative_1728_);
lean_inc(v_toBind_1729_);
v___f_1731_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1731_, 0, v_toBind_1729_);
lean_inc(v_toPure_1730_);
v___f_1732_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1732_, 0, v_toPure_1730_);
v___x_1733_ = lean_box(0);
lean_inc(v_toPure_1730_);
v___f_1734_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1734_, 0, v___x_1733_);
lean_closure_set(v___f_1734_, 1, v_toPure_1730_);
v___f_1735_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1735_, 0, v_f_1727_);
lean_closure_set(v___f_1735_, 1, v_toPure_1730_);
lean_closure_set(v___f_1735_, 2, v_toBind_1729_);
lean_closure_set(v___f_1735_, 3, v___f_1734_);
lean_closure_set(v___f_1735_, 4, v___f_1732_);
v___x_1736_ = lean_apply_6(v_inst_1724_, v___f_1731_, lean_box(0), lean_box(0), v_it_1726_, v___x_1733_, v___f_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f___boxed(lean_object* v_00_u03b1_1737_, lean_object* v_00_u03b2_1738_, lean_object* v_00_u03b3_1739_, lean_object* v_m_1740_, lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_inst_1743_, lean_object* v_inst_1744_, lean_object* v_it_1745_, lean_object* v_f_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Std_IterM_Total_findSome_x3f(v_00_u03b1_1737_, v_00_u03b2_1738_, v_00_u03b3_1739_, v_m_1740_, v_inst_1741_, v_inst_1742_, v_inst_1743_, v_inst_1744_, v_it_1745_, v_f_1746_);
lean_dec(v_inst_1742_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__3(lean_object* v_toPure_1748_, lean_object* v___x_1749_, lean_object* v_x1_1750_, uint8_t v_____do__lift_1751_){
_start:
{
if (v_____do__lift_1751_ == 0)
{
lean_object* v___x_1752_; 
lean_dec(v_x1_1750_);
v___x_1752_ = lean_apply_2(v_toPure_1748_, lean_box(0), v___x_1749_);
return v___x_1752_;
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec(v___x_1749_);
v___x_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_x1_1750_);
v___x_1754_ = lean_apply_2(v_toPure_1748_, lean_box(0), v___x_1753_);
return v___x_1754_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__3___boxed(lean_object* v_toPure_1755_, lean_object* v___x_1756_, lean_object* v_x1_1757_, lean_object* v_____do__lift_1758_){
_start:
{
uint8_t v_____do__lift_191__boxed_1759_; lean_object* v_res_1760_; 
v_____do__lift_191__boxed_1759_ = lean_unbox(v_____do__lift_1758_);
v_res_1760_ = l_Std_IterM_findM_x3f___redArg___lam__3(v_toPure_1755_, v___x_1756_, v_x1_1757_, v_____do__lift_191__boxed_1759_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__0(lean_object* v_toPure_1761_, lean_object* v___x_1762_, lean_object* v_f_1763_, lean_object* v_toBind_1764_, lean_object* v___f_1765_, lean_object* v___f_1766_, lean_object* v_x1_1767_, lean_object* v_x2_1768_, lean_object* v_x3_1769_){
_start:
{
lean_object* v___f_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
lean_inc(v_x1_1767_);
v___f_1770_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_1770_, 0, v_toPure_1761_);
lean_closure_set(v___f_1770_, 1, v___x_1762_);
lean_closure_set(v___f_1770_, 2, v_x1_1767_);
v___x_1771_ = lean_apply_1(v_f_1763_, v_x1_1767_);
lean_inc(v_toBind_1764_);
v___x_1772_ = lean_apply_4(v_toBind_1764_, lean_box(0), lean_box(0), v___x_1771_, v___f_1770_);
lean_inc(v_toBind_1764_);
v___x_1773_ = lean_apply_4(v_toBind_1764_, lean_box(0), lean_box(0), v___x_1772_, v___f_1765_);
v___x_1774_ = lean_apply_4(v_toBind_1764_, lean_box(0), lean_box(0), v___x_1773_, v___f_1766_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_1775_, lean_object* v___x_1776_, lean_object* v_f_1777_, lean_object* v_toBind_1778_, lean_object* v___f_1779_, lean_object* v___f_1780_, lean_object* v_x1_1781_, lean_object* v_x2_1782_, lean_object* v_x3_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Std_IterM_findM_x3f___redArg___lam__0(v_toPure_1775_, v___x_1776_, v_f_1777_, v_toBind_1778_, v___f_1779_, v___f_1780_, v_x1_1781_, v_x2_1782_, v_x3_1783_);
lean_dec(v_x3_1783_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg(lean_object* v_inst_1785_, lean_object* v_inst_1786_, lean_object* v_it_1787_, lean_object* v_f_1788_){
_start:
{
lean_object* v_toApplicative_1789_; lean_object* v_toBind_1790_; lean_object* v_toPure_1791_; lean_object* v___f_1792_; lean_object* v___f_1793_; lean_object* v___x_1794_; lean_object* v___f_1795_; lean_object* v___f_1796_; lean_object* v___x_1797_; 
v_toApplicative_1789_ = lean_ctor_get(v_inst_1785_, 0);
lean_inc_ref(v_toApplicative_1789_);
v_toBind_1790_ = lean_ctor_get(v_inst_1785_, 1);
lean_inc(v_toBind_1790_);
lean_dec_ref(v_inst_1785_);
v_toPure_1791_ = lean_ctor_get(v_toApplicative_1789_, 1);
lean_inc(v_toPure_1791_);
lean_dec_ref(v_toApplicative_1789_);
lean_inc(v_toBind_1790_);
v___f_1792_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1792_, 0, v_toBind_1790_);
lean_inc(v_toPure_1791_);
v___f_1793_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1793_, 0, v_toPure_1791_);
v___x_1794_ = lean_box(0);
lean_inc(v_toPure_1791_);
v___f_1795_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1795_, 0, v___x_1794_);
lean_closure_set(v___f_1795_, 1, v_toPure_1791_);
v___f_1796_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1796_, 0, v_toPure_1791_);
lean_closure_set(v___f_1796_, 1, v___x_1794_);
lean_closure_set(v___f_1796_, 2, v_f_1788_);
lean_closure_set(v___f_1796_, 3, v_toBind_1790_);
lean_closure_set(v___f_1796_, 4, v___f_1795_);
lean_closure_set(v___f_1796_, 5, v___f_1793_);
v___x_1797_ = lean_apply_6(v_inst_1786_, v___f_1792_, lean_box(0), lean_box(0), v_it_1787_, v___x_1794_, v___f_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f(lean_object* v_00_u03b1_1798_, lean_object* v_00_u03b2_1799_, lean_object* v_m_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_it_1804_, lean_object* v_f_1805_){
_start:
{
lean_object* v_toApplicative_1806_; lean_object* v_toBind_1807_; lean_object* v_toPure_1808_; lean_object* v___f_1809_; lean_object* v___f_1810_; lean_object* v___x_1811_; lean_object* v___f_1812_; lean_object* v___f_1813_; lean_object* v___x_1814_; 
v_toApplicative_1806_ = lean_ctor_get(v_inst_1801_, 0);
lean_inc_ref(v_toApplicative_1806_);
v_toBind_1807_ = lean_ctor_get(v_inst_1801_, 1);
lean_inc(v_toBind_1807_);
lean_dec_ref(v_inst_1801_);
v_toPure_1808_ = lean_ctor_get(v_toApplicative_1806_, 1);
lean_inc(v_toPure_1808_);
lean_dec_ref(v_toApplicative_1806_);
lean_inc(v_toBind_1807_);
v___f_1809_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1809_, 0, v_toBind_1807_);
lean_inc(v_toPure_1808_);
v___f_1810_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1810_, 0, v_toPure_1808_);
v___x_1811_ = lean_box(0);
lean_inc(v_toPure_1808_);
v___f_1812_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1812_, 0, v___x_1811_);
lean_closure_set(v___f_1812_, 1, v_toPure_1808_);
v___f_1813_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1813_, 0, v_toPure_1808_);
lean_closure_set(v___f_1813_, 1, v___x_1811_);
lean_closure_set(v___f_1813_, 2, v_f_1805_);
lean_closure_set(v___f_1813_, 3, v_toBind_1807_);
lean_closure_set(v___f_1813_, 4, v___f_1812_);
lean_closure_set(v___f_1813_, 5, v___f_1810_);
v___x_1814_ = lean_apply_6(v_inst_1803_, v___f_1809_, lean_box(0), lean_box(0), v_it_1804_, v___x_1811_, v___f_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___boxed(lean_object* v_00_u03b1_1815_, lean_object* v_00_u03b2_1816_, lean_object* v_m_1817_, lean_object* v_inst_1818_, lean_object* v_inst_1819_, lean_object* v_inst_1820_, lean_object* v_it_1821_, lean_object* v_f_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Std_IterM_findM_x3f(v_00_u03b1_1815_, v_00_u03b2_1816_, v_m_1817_, v_inst_1818_, v_inst_1819_, v_inst_1820_, v_it_1821_, v_f_1822_);
lean_dec(v_inst_1819_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f___redArg(lean_object* v_inst_1824_, lean_object* v_inst_1825_, lean_object* v_it_1826_, lean_object* v_f_1827_){
_start:
{
lean_object* v_toApplicative_1828_; lean_object* v_toBind_1829_; lean_object* v_toPure_1830_; lean_object* v___f_1831_; lean_object* v___f_1832_; lean_object* v___x_1833_; lean_object* v___f_1834_; lean_object* v___f_1835_; lean_object* v___x_1836_; 
v_toApplicative_1828_ = lean_ctor_get(v_inst_1824_, 0);
lean_inc_ref(v_toApplicative_1828_);
v_toBind_1829_ = lean_ctor_get(v_inst_1824_, 1);
lean_inc(v_toBind_1829_);
lean_dec_ref(v_inst_1824_);
v_toPure_1830_ = lean_ctor_get(v_toApplicative_1828_, 1);
lean_inc(v_toPure_1830_);
lean_dec_ref(v_toApplicative_1828_);
lean_inc(v_toBind_1829_);
v___f_1831_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1831_, 0, v_toBind_1829_);
lean_inc(v_toPure_1830_);
v___f_1832_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1832_, 0, v_toPure_1830_);
v___x_1833_ = lean_box(0);
lean_inc(v_toPure_1830_);
v___f_1834_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1834_, 0, v___x_1833_);
lean_closure_set(v___f_1834_, 1, v_toPure_1830_);
v___f_1835_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1835_, 0, v_toPure_1830_);
lean_closure_set(v___f_1835_, 1, v___x_1833_);
lean_closure_set(v___f_1835_, 2, v_f_1827_);
lean_closure_set(v___f_1835_, 3, v_toBind_1829_);
lean_closure_set(v___f_1835_, 4, v___f_1834_);
lean_closure_set(v___f_1835_, 5, v___f_1832_);
v___x_1836_ = lean_apply_6(v_inst_1825_, v___f_1831_, lean_box(0), lean_box(0), v_it_1826_, v___x_1833_, v___f_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f(lean_object* v_00_u03b1_1837_, lean_object* v_00_u03b2_1838_, lean_object* v_m_1839_, lean_object* v_inst_1840_, lean_object* v_inst_1841_, lean_object* v_inst_1842_, lean_object* v_it_1843_, lean_object* v_f_1844_){
_start:
{
lean_object* v_toApplicative_1845_; lean_object* v_toBind_1846_; lean_object* v_toPure_1847_; lean_object* v___f_1848_; lean_object* v___f_1849_; lean_object* v___x_1850_; lean_object* v___f_1851_; lean_object* v___f_1852_; lean_object* v___x_1853_; 
v_toApplicative_1845_ = lean_ctor_get(v_inst_1840_, 0);
lean_inc_ref(v_toApplicative_1845_);
v_toBind_1846_ = lean_ctor_get(v_inst_1840_, 1);
lean_inc(v_toBind_1846_);
lean_dec_ref(v_inst_1840_);
v_toPure_1847_ = lean_ctor_get(v_toApplicative_1845_, 1);
lean_inc(v_toPure_1847_);
lean_dec_ref(v_toApplicative_1845_);
lean_inc(v_toBind_1846_);
v___f_1848_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1848_, 0, v_toBind_1846_);
lean_inc(v_toPure_1847_);
v___f_1849_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1849_, 0, v_toPure_1847_);
v___x_1850_ = lean_box(0);
lean_inc(v_toPure_1847_);
v___f_1851_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1851_, 0, v___x_1850_);
lean_closure_set(v___f_1851_, 1, v_toPure_1847_);
v___f_1852_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1852_, 0, v_toPure_1847_);
lean_closure_set(v___f_1852_, 1, v___x_1850_);
lean_closure_set(v___f_1852_, 2, v_f_1844_);
lean_closure_set(v___f_1852_, 3, v_toBind_1846_);
lean_closure_set(v___f_1852_, 4, v___f_1851_);
lean_closure_set(v___f_1852_, 5, v___f_1849_);
v___x_1853_ = lean_apply_6(v_inst_1842_, v___f_1848_, lean_box(0), lean_box(0), v_it_1843_, v___x_1850_, v___f_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f___boxed(lean_object* v_00_u03b1_1854_, lean_object* v_00_u03b2_1855_, lean_object* v_m_1856_, lean_object* v_inst_1857_, lean_object* v_inst_1858_, lean_object* v_inst_1859_, lean_object* v_it_1860_, lean_object* v_f_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Std_IterM_Partial_findM_x3f(v_00_u03b1_1854_, v_00_u03b2_1855_, v_m_1856_, v_inst_1857_, v_inst_1858_, v_inst_1859_, v_it_1860_, v_f_1861_);
lean_dec(v_inst_1858_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f___redArg(lean_object* v_inst_1863_, lean_object* v_inst_1864_, lean_object* v_it_1865_, lean_object* v_f_1866_){
_start:
{
lean_object* v_toApplicative_1867_; lean_object* v_toBind_1868_; lean_object* v_toPure_1869_; lean_object* v___f_1870_; lean_object* v___f_1871_; lean_object* v___x_1872_; lean_object* v___f_1873_; lean_object* v___f_1874_; lean_object* v___x_1875_; 
v_toApplicative_1867_ = lean_ctor_get(v_inst_1863_, 0);
lean_inc_ref(v_toApplicative_1867_);
v_toBind_1868_ = lean_ctor_get(v_inst_1863_, 1);
lean_inc(v_toBind_1868_);
lean_dec_ref(v_inst_1863_);
v_toPure_1869_ = lean_ctor_get(v_toApplicative_1867_, 1);
lean_inc(v_toPure_1869_);
lean_dec_ref(v_toApplicative_1867_);
lean_inc(v_toBind_1868_);
v___f_1870_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1870_, 0, v_toBind_1868_);
lean_inc(v_toPure_1869_);
v___f_1871_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1871_, 0, v_toPure_1869_);
v___x_1872_ = lean_box(0);
lean_inc(v_toPure_1869_);
v___f_1873_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1873_, 0, v___x_1872_);
lean_closure_set(v___f_1873_, 1, v_toPure_1869_);
v___f_1874_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1874_, 0, v_toPure_1869_);
lean_closure_set(v___f_1874_, 1, v___x_1872_);
lean_closure_set(v___f_1874_, 2, v_f_1866_);
lean_closure_set(v___f_1874_, 3, v_toBind_1868_);
lean_closure_set(v___f_1874_, 4, v___f_1873_);
lean_closure_set(v___f_1874_, 5, v___f_1871_);
v___x_1875_ = lean_apply_6(v_inst_1864_, v___f_1870_, lean_box(0), lean_box(0), v_it_1865_, v___x_1872_, v___f_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f(lean_object* v_00_u03b1_1876_, lean_object* v_00_u03b2_1877_, lean_object* v_m_1878_, lean_object* v_inst_1879_, lean_object* v_inst_1880_, lean_object* v_inst_1881_, lean_object* v_inst_1882_, lean_object* v_it_1883_, lean_object* v_f_1884_){
_start:
{
lean_object* v_toApplicative_1885_; lean_object* v_toBind_1886_; lean_object* v_toPure_1887_; lean_object* v___f_1888_; lean_object* v___f_1889_; lean_object* v___x_1890_; lean_object* v___f_1891_; lean_object* v___f_1892_; lean_object* v___x_1893_; 
v_toApplicative_1885_ = lean_ctor_get(v_inst_1879_, 0);
lean_inc_ref(v_toApplicative_1885_);
v_toBind_1886_ = lean_ctor_get(v_inst_1879_, 1);
lean_inc(v_toBind_1886_);
lean_dec_ref(v_inst_1879_);
v_toPure_1887_ = lean_ctor_get(v_toApplicative_1885_, 1);
lean_inc(v_toPure_1887_);
lean_dec_ref(v_toApplicative_1885_);
lean_inc(v_toBind_1886_);
v___f_1888_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1888_, 0, v_toBind_1886_);
lean_inc(v_toPure_1887_);
v___f_1889_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1889_, 0, v_toPure_1887_);
v___x_1890_ = lean_box(0);
lean_inc(v_toPure_1887_);
v___f_1891_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1891_, 0, v___x_1890_);
lean_closure_set(v___f_1891_, 1, v_toPure_1887_);
v___f_1892_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1892_, 0, v_toPure_1887_);
lean_closure_set(v___f_1892_, 1, v___x_1890_);
lean_closure_set(v___f_1892_, 2, v_f_1884_);
lean_closure_set(v___f_1892_, 3, v_toBind_1886_);
lean_closure_set(v___f_1892_, 4, v___f_1891_);
lean_closure_set(v___f_1892_, 5, v___f_1889_);
v___x_1893_ = lean_apply_6(v_inst_1881_, v___f_1888_, lean_box(0), lean_box(0), v_it_1883_, v___x_1890_, v___f_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f___boxed(lean_object* v_00_u03b1_1894_, lean_object* v_00_u03b2_1895_, lean_object* v_m_1896_, lean_object* v_inst_1897_, lean_object* v_inst_1898_, lean_object* v_inst_1899_, lean_object* v_inst_1900_, lean_object* v_it_1901_, lean_object* v_f_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Std_IterM_Total_findM_x3f(v_00_u03b1_1894_, v_00_u03b2_1895_, v_m_1896_, v_inst_1897_, v_inst_1898_, v_inst_1899_, v_inst_1900_, v_it_1901_, v_f_1902_);
lean_dec(v_inst_1898_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg___lam__4(lean_object* v_toPure_1904_, lean_object* v___x_1905_, lean_object* v_f_1906_, lean_object* v_toBind_1907_, lean_object* v___f_1908_, lean_object* v___f_1909_, lean_object* v_x1_1910_, lean_object* v_x2_1911_, lean_object* v_x3_1912_){
_start:
{
lean_object* v___f_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
lean_inc(v_x1_1910_);
lean_inc(v_toPure_1904_);
v___f_1913_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_1913_, 0, v_toPure_1904_);
lean_closure_set(v___f_1913_, 1, v___x_1905_);
lean_closure_set(v___f_1913_, 2, v_x1_1910_);
v___x_1914_ = lean_apply_1(v_f_1906_, v_x1_1910_);
v___x_1915_ = lean_apply_2(v_toPure_1904_, lean_box(0), v___x_1914_);
lean_inc(v_toBind_1907_);
v___x_1916_ = lean_apply_4(v_toBind_1907_, lean_box(0), lean_box(0), v___x_1915_, v___f_1913_);
lean_inc(v_toBind_1907_);
v___x_1917_ = lean_apply_4(v_toBind_1907_, lean_box(0), lean_box(0), v___x_1916_, v___f_1908_);
v___x_1918_ = lean_apply_4(v_toBind_1907_, lean_box(0), lean_box(0), v___x_1917_, v___f_1909_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg___lam__4___boxed(lean_object* v_toPure_1919_, lean_object* v___x_1920_, lean_object* v_f_1921_, lean_object* v_toBind_1922_, lean_object* v___f_1923_, lean_object* v___f_1924_, lean_object* v_x1_1925_, lean_object* v_x2_1926_, lean_object* v_x3_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Std_IterM_find_x3f___redArg___lam__4(v_toPure_1919_, v___x_1920_, v_f_1921_, v_toBind_1922_, v___f_1923_, v___f_1924_, v_x1_1925_, v_x2_1926_, v_x3_1927_);
lean_dec(v_x3_1927_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg(lean_object* v_inst_1929_, lean_object* v_inst_1930_, lean_object* v_it_1931_, lean_object* v_f_1932_){
_start:
{
lean_object* v_toApplicative_1933_; lean_object* v_toBind_1934_; lean_object* v_toPure_1935_; lean_object* v___f_1936_; lean_object* v___f_1937_; lean_object* v___x_1938_; lean_object* v___f_1939_; lean_object* v___f_1940_; lean_object* v___x_1941_; 
v_toApplicative_1933_ = lean_ctor_get(v_inst_1929_, 0);
lean_inc_ref(v_toApplicative_1933_);
v_toBind_1934_ = lean_ctor_get(v_inst_1929_, 1);
lean_inc(v_toBind_1934_);
lean_dec_ref(v_inst_1929_);
v_toPure_1935_ = lean_ctor_get(v_toApplicative_1933_, 1);
lean_inc(v_toPure_1935_);
lean_dec_ref(v_toApplicative_1933_);
lean_inc(v_toBind_1934_);
v___f_1936_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1936_, 0, v_toBind_1934_);
lean_inc(v_toPure_1935_);
v___f_1937_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1937_, 0, v_toPure_1935_);
v___x_1938_ = lean_box(0);
lean_inc(v_toPure_1935_);
v___f_1939_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1939_, 0, v___x_1938_);
lean_closure_set(v___f_1939_, 1, v_toPure_1935_);
v___f_1940_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_1940_, 0, v_toPure_1935_);
lean_closure_set(v___f_1940_, 1, v___x_1938_);
lean_closure_set(v___f_1940_, 2, v_f_1932_);
lean_closure_set(v___f_1940_, 3, v_toBind_1934_);
lean_closure_set(v___f_1940_, 4, v___f_1939_);
lean_closure_set(v___f_1940_, 5, v___f_1937_);
v___x_1941_ = lean_apply_6(v_inst_1930_, v___f_1936_, lean_box(0), lean_box(0), v_it_1931_, v___x_1938_, v___f_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f(lean_object* v_00_u03b1_1942_, lean_object* v_00_u03b2_1943_, lean_object* v_m_1944_, lean_object* v_inst_1945_, lean_object* v_inst_1946_, lean_object* v_inst_1947_, lean_object* v_it_1948_, lean_object* v_f_1949_){
_start:
{
lean_object* v_toApplicative_1950_; lean_object* v_toBind_1951_; lean_object* v_toPure_1952_; lean_object* v___f_1953_; lean_object* v___f_1954_; lean_object* v___x_1955_; lean_object* v___f_1956_; lean_object* v___f_1957_; lean_object* v___x_1958_; 
v_toApplicative_1950_ = lean_ctor_get(v_inst_1945_, 0);
lean_inc_ref(v_toApplicative_1950_);
v_toBind_1951_ = lean_ctor_get(v_inst_1945_, 1);
lean_inc(v_toBind_1951_);
lean_dec_ref(v_inst_1945_);
v_toPure_1952_ = lean_ctor_get(v_toApplicative_1950_, 1);
lean_inc(v_toPure_1952_);
lean_dec_ref(v_toApplicative_1950_);
lean_inc(v_toBind_1951_);
v___f_1953_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1953_, 0, v_toBind_1951_);
lean_inc(v_toPure_1952_);
v___f_1954_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1954_, 0, v_toPure_1952_);
v___x_1955_ = lean_box(0);
lean_inc(v_toPure_1952_);
v___f_1956_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1956_, 0, v___x_1955_);
lean_closure_set(v___f_1956_, 1, v_toPure_1952_);
v___f_1957_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_1957_, 0, v_toPure_1952_);
lean_closure_set(v___f_1957_, 1, v___x_1955_);
lean_closure_set(v___f_1957_, 2, v_f_1949_);
lean_closure_set(v___f_1957_, 3, v_toBind_1951_);
lean_closure_set(v___f_1957_, 4, v___f_1956_);
lean_closure_set(v___f_1957_, 5, v___f_1954_);
v___x_1958_ = lean_apply_6(v_inst_1947_, v___f_1953_, lean_box(0), lean_box(0), v_it_1948_, v___x_1955_, v___f_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___boxed(lean_object* v_00_u03b1_1959_, lean_object* v_00_u03b2_1960_, lean_object* v_m_1961_, lean_object* v_inst_1962_, lean_object* v_inst_1963_, lean_object* v_inst_1964_, lean_object* v_it_1965_, lean_object* v_f_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Std_IterM_find_x3f(v_00_u03b1_1959_, v_00_u03b2_1960_, v_m_1961_, v_inst_1962_, v_inst_1963_, v_inst_1964_, v_it_1965_, v_f_1966_);
lean_dec(v_inst_1963_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f___redArg(lean_object* v_inst_1968_, lean_object* v_inst_1969_, lean_object* v_it_1970_, lean_object* v_f_1971_){
_start:
{
lean_object* v_toApplicative_1972_; lean_object* v_toBind_1973_; lean_object* v_toPure_1974_; lean_object* v___f_1975_; lean_object* v___f_1976_; lean_object* v___x_1977_; lean_object* v___f_1978_; lean_object* v___f_1979_; lean_object* v___x_1980_; 
v_toApplicative_1972_ = lean_ctor_get(v_inst_1968_, 0);
lean_inc_ref(v_toApplicative_1972_);
v_toBind_1973_ = lean_ctor_get(v_inst_1968_, 1);
lean_inc(v_toBind_1973_);
lean_dec_ref(v_inst_1968_);
v_toPure_1974_ = lean_ctor_get(v_toApplicative_1972_, 1);
lean_inc(v_toPure_1974_);
lean_dec_ref(v_toApplicative_1972_);
lean_inc(v_toBind_1973_);
v___f_1975_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1975_, 0, v_toBind_1973_);
lean_inc(v_toPure_1974_);
v___f_1976_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1976_, 0, v_toPure_1974_);
v___x_1977_ = lean_box(0);
lean_inc(v_toPure_1974_);
v___f_1978_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1978_, 0, v___x_1977_);
lean_closure_set(v___f_1978_, 1, v_toPure_1974_);
v___f_1979_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_1979_, 0, v_toPure_1974_);
lean_closure_set(v___f_1979_, 1, v___x_1977_);
lean_closure_set(v___f_1979_, 2, v_f_1971_);
lean_closure_set(v___f_1979_, 3, v_toBind_1973_);
lean_closure_set(v___f_1979_, 4, v___f_1978_);
lean_closure_set(v___f_1979_, 5, v___f_1976_);
v___x_1980_ = lean_apply_6(v_inst_1969_, v___f_1975_, lean_box(0), lean_box(0), v_it_1970_, v___x_1977_, v___f_1979_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f(lean_object* v_00_u03b1_1981_, lean_object* v_00_u03b2_1982_, lean_object* v_m_1983_, lean_object* v_inst_1984_, lean_object* v_inst_1985_, lean_object* v_inst_1986_, lean_object* v_it_1987_, lean_object* v_f_1988_){
_start:
{
lean_object* v_toApplicative_1989_; lean_object* v_toBind_1990_; lean_object* v_toPure_1991_; lean_object* v___f_1992_; lean_object* v___f_1993_; lean_object* v___x_1994_; lean_object* v___f_1995_; lean_object* v___f_1996_; lean_object* v___x_1997_; 
v_toApplicative_1989_ = lean_ctor_get(v_inst_1984_, 0);
lean_inc_ref(v_toApplicative_1989_);
v_toBind_1990_ = lean_ctor_get(v_inst_1984_, 1);
lean_inc(v_toBind_1990_);
lean_dec_ref(v_inst_1984_);
v_toPure_1991_ = lean_ctor_get(v_toApplicative_1989_, 1);
lean_inc(v_toPure_1991_);
lean_dec_ref(v_toApplicative_1989_);
lean_inc(v_toBind_1990_);
v___f_1992_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1992_, 0, v_toBind_1990_);
lean_inc(v_toPure_1991_);
v___f_1993_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1993_, 0, v_toPure_1991_);
v___x_1994_ = lean_box(0);
lean_inc(v_toPure_1991_);
v___f_1995_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1995_, 0, v___x_1994_);
lean_closure_set(v___f_1995_, 1, v_toPure_1991_);
v___f_1996_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_1996_, 0, v_toPure_1991_);
lean_closure_set(v___f_1996_, 1, v___x_1994_);
lean_closure_set(v___f_1996_, 2, v_f_1988_);
lean_closure_set(v___f_1996_, 3, v_toBind_1990_);
lean_closure_set(v___f_1996_, 4, v___f_1995_);
lean_closure_set(v___f_1996_, 5, v___f_1993_);
v___x_1997_ = lean_apply_6(v_inst_1986_, v___f_1992_, lean_box(0), lean_box(0), v_it_1987_, v___x_1994_, v___f_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f___boxed(lean_object* v_00_u03b1_1998_, lean_object* v_00_u03b2_1999_, lean_object* v_m_2000_, lean_object* v_inst_2001_, lean_object* v_inst_2002_, lean_object* v_inst_2003_, lean_object* v_it_2004_, lean_object* v_f_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Std_IterM_Partial_find_x3f(v_00_u03b1_1998_, v_00_u03b2_1999_, v_m_2000_, v_inst_2001_, v_inst_2002_, v_inst_2003_, v_it_2004_, v_f_2005_);
lean_dec(v_inst_2002_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f___redArg(lean_object* v_inst_2007_, lean_object* v_inst_2008_, lean_object* v_it_2009_, lean_object* v_f_2010_){
_start:
{
lean_object* v_toApplicative_2011_; lean_object* v_toBind_2012_; lean_object* v_toPure_2013_; lean_object* v___f_2014_; lean_object* v___f_2015_; lean_object* v___x_2016_; lean_object* v___f_2017_; lean_object* v___f_2018_; lean_object* v___x_2019_; 
v_toApplicative_2011_ = lean_ctor_get(v_inst_2007_, 0);
lean_inc_ref(v_toApplicative_2011_);
v_toBind_2012_ = lean_ctor_get(v_inst_2007_, 1);
lean_inc(v_toBind_2012_);
lean_dec_ref(v_inst_2007_);
v_toPure_2013_ = lean_ctor_get(v_toApplicative_2011_, 1);
lean_inc(v_toPure_2013_);
lean_dec_ref(v_toApplicative_2011_);
lean_inc(v_toBind_2012_);
v___f_2014_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2014_, 0, v_toBind_2012_);
lean_inc(v_toPure_2013_);
v___f_2015_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2015_, 0, v_toPure_2013_);
v___x_2016_ = lean_box(0);
lean_inc(v_toPure_2013_);
v___f_2017_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2017_, 0, v___x_2016_);
lean_closure_set(v___f_2017_, 1, v_toPure_2013_);
v___f_2018_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_2018_, 0, v_toPure_2013_);
lean_closure_set(v___f_2018_, 1, v___x_2016_);
lean_closure_set(v___f_2018_, 2, v_f_2010_);
lean_closure_set(v___f_2018_, 3, v_toBind_2012_);
lean_closure_set(v___f_2018_, 4, v___f_2017_);
lean_closure_set(v___f_2018_, 5, v___f_2015_);
v___x_2019_ = lean_apply_6(v_inst_2008_, v___f_2014_, lean_box(0), lean_box(0), v_it_2009_, v___x_2016_, v___f_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f(lean_object* v_00_u03b1_2020_, lean_object* v_00_u03b2_2021_, lean_object* v_m_2022_, lean_object* v_inst_2023_, lean_object* v_inst_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_it_2027_, lean_object* v_f_2028_){
_start:
{
lean_object* v_toApplicative_2029_; lean_object* v_toBind_2030_; lean_object* v_toPure_2031_; lean_object* v___f_2032_; lean_object* v___f_2033_; lean_object* v___x_2034_; lean_object* v___f_2035_; lean_object* v___f_2036_; lean_object* v___x_2037_; 
v_toApplicative_2029_ = lean_ctor_get(v_inst_2023_, 0);
lean_inc_ref(v_toApplicative_2029_);
v_toBind_2030_ = lean_ctor_get(v_inst_2023_, 1);
lean_inc(v_toBind_2030_);
lean_dec_ref(v_inst_2023_);
v_toPure_2031_ = lean_ctor_get(v_toApplicative_2029_, 1);
lean_inc(v_toPure_2031_);
lean_dec_ref(v_toApplicative_2029_);
lean_inc(v_toBind_2030_);
v___f_2032_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2032_, 0, v_toBind_2030_);
lean_inc(v_toPure_2031_);
v___f_2033_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2033_, 0, v_toPure_2031_);
v___x_2034_ = lean_box(0);
lean_inc(v_toPure_2031_);
v___f_2035_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2035_, 0, v___x_2034_);
lean_closure_set(v___f_2035_, 1, v_toPure_2031_);
v___f_2036_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_2036_, 0, v_toPure_2031_);
lean_closure_set(v___f_2036_, 1, v___x_2034_);
lean_closure_set(v___f_2036_, 2, v_f_2028_);
lean_closure_set(v___f_2036_, 3, v_toBind_2030_);
lean_closure_set(v___f_2036_, 4, v___f_2035_);
lean_closure_set(v___f_2036_, 5, v___f_2033_);
v___x_2037_ = lean_apply_6(v_inst_2025_, v___f_2032_, lean_box(0), lean_box(0), v_it_2027_, v___x_2034_, v___f_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f___boxed(lean_object* v_00_u03b1_2038_, lean_object* v_00_u03b2_2039_, lean_object* v_m_2040_, lean_object* v_inst_2041_, lean_object* v_inst_2042_, lean_object* v_inst_2043_, lean_object* v_inst_2044_, lean_object* v_it_2045_, lean_object* v_f_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Std_IterM_Total_find_x3f(v_00_u03b1_2038_, v_00_u03b2_2039_, v_m_2040_, v_inst_2041_, v_inst_2042_, v_inst_2043_, v_inst_2044_, v_it_2045_, v_f_2046_);
lean_dec(v_inst_2042_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg___lam__0(lean_object* v_toBind_2048_, lean_object* v_x_2049_, lean_object* v_x_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = lean_apply_4(v_toBind_2048_, lean_box(0), lean_box(0), v___y_2052_, v___y_2051_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg___lam__1(lean_object* v_toPure_2054_, lean_object* v_b_2055_, lean_object* v_x_2056_, lean_object* v_x_2057_){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2058_, 0, v_b_2055_);
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
v___x_2060_ = lean_apply_2(v_toPure_2054_, lean_box(0), v___x_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg___lam__1___boxed(lean_object* v_toPure_2061_, lean_object* v_b_2062_, lean_object* v_x_2063_, lean_object* v_x_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Std_IterM_first_x3f___redArg___lam__1(v_toPure_2061_, v_b_2062_, v_x_2063_, v_x_2064_);
lean_dec(v_x_2064_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg(lean_object* v_inst_2066_, lean_object* v_inst_2067_, lean_object* v_it_2068_){
_start:
{
lean_object* v_toApplicative_2069_; lean_object* v_toBind_2070_; lean_object* v_toPure_2071_; lean_object* v___f_2072_; lean_object* v___f_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v_toApplicative_2069_ = lean_ctor_get(v_inst_2066_, 0);
lean_inc_ref(v_toApplicative_2069_);
v_toBind_2070_ = lean_ctor_get(v_inst_2066_, 1);
lean_inc(v_toBind_2070_);
lean_dec_ref(v_inst_2066_);
v_toPure_2071_ = lean_ctor_get(v_toApplicative_2069_, 1);
lean_inc(v_toPure_2071_);
lean_dec_ref(v_toApplicative_2069_);
v___f_2072_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2072_, 0, v_toBind_2070_);
v___f_2073_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2073_, 0, v_toPure_2071_);
v___x_2074_ = lean_box(0);
v___x_2075_ = lean_apply_6(v_inst_2067_, v___f_2072_, lean_box(0), lean_box(0), v_it_2068_, v___x_2074_, v___f_2073_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f(lean_object* v_00_u03b1_2076_, lean_object* v_00_u03b2_2077_, lean_object* v_m_2078_, lean_object* v_inst_2079_, lean_object* v_inst_2080_, lean_object* v_inst_2081_, lean_object* v_it_2082_){
_start:
{
lean_object* v_toApplicative_2083_; lean_object* v_toBind_2084_; lean_object* v_toPure_2085_; lean_object* v___f_2086_; lean_object* v___f_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v_toApplicative_2083_ = lean_ctor_get(v_inst_2079_, 0);
lean_inc_ref(v_toApplicative_2083_);
v_toBind_2084_ = lean_ctor_get(v_inst_2079_, 1);
lean_inc(v_toBind_2084_);
lean_dec_ref(v_inst_2079_);
v_toPure_2085_ = lean_ctor_get(v_toApplicative_2083_, 1);
lean_inc(v_toPure_2085_);
lean_dec_ref(v_toApplicative_2083_);
v___f_2086_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2086_, 0, v_toBind_2084_);
v___f_2087_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2087_, 0, v_toPure_2085_);
v___x_2088_ = lean_box(0);
v___x_2089_ = lean_apply_6(v_inst_2081_, v___f_2086_, lean_box(0), lean_box(0), v_it_2082_, v___x_2088_, v___f_2087_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___boxed(lean_object* v_00_u03b1_2090_, lean_object* v_00_u03b2_2091_, lean_object* v_m_2092_, lean_object* v_inst_2093_, lean_object* v_inst_2094_, lean_object* v_inst_2095_, lean_object* v_it_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Std_IterM_first_x3f(v_00_u03b1_2090_, v_00_u03b2_2091_, v_m_2092_, v_inst_2093_, v_inst_2094_, v_inst_2095_, v_it_2096_);
lean_dec(v_inst_2094_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_first_x3f___redArg(lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_it_2100_){
_start:
{
lean_object* v_toApplicative_2101_; lean_object* v_toBind_2102_; lean_object* v_toPure_2103_; lean_object* v___f_2104_; lean_object* v___f_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v_toApplicative_2101_ = lean_ctor_get(v_inst_2098_, 0);
lean_inc_ref(v_toApplicative_2101_);
v_toBind_2102_ = lean_ctor_get(v_inst_2098_, 1);
lean_inc(v_toBind_2102_);
lean_dec_ref(v_inst_2098_);
v_toPure_2103_ = lean_ctor_get(v_toApplicative_2101_, 1);
lean_inc(v_toPure_2103_);
lean_dec_ref(v_toApplicative_2101_);
v___f_2104_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2104_, 0, v_toBind_2102_);
v___f_2105_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2105_, 0, v_toPure_2103_);
v___x_2106_ = lean_box(0);
v___x_2107_ = lean_apply_6(v_inst_2099_, v___f_2104_, lean_box(0), lean_box(0), v_it_2100_, v___x_2106_, v___f_2105_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_first_x3f(lean_object* v_00_u03b1_2108_, lean_object* v_00_u03b2_2109_, lean_object* v_m_2110_, lean_object* v_inst_2111_, lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_inst_2114_, lean_object* v_it_2115_){
_start:
{
lean_object* v_toApplicative_2116_; lean_object* v_toBind_2117_; lean_object* v_toPure_2118_; lean_object* v___f_2119_; lean_object* v___f_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_toApplicative_2116_ = lean_ctor_get(v_inst_2111_, 0);
lean_inc_ref(v_toApplicative_2116_);
v_toBind_2117_ = lean_ctor_get(v_inst_2111_, 1);
lean_inc(v_toBind_2117_);
lean_dec_ref(v_inst_2111_);
v_toPure_2118_ = lean_ctor_get(v_toApplicative_2116_, 1);
lean_inc(v_toPure_2118_);
lean_dec_ref(v_toApplicative_2116_);
v___f_2119_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2119_, 0, v_toBind_2117_);
v___f_2120_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2120_, 0, v_toPure_2118_);
v___x_2121_ = lean_box(0);
v___x_2122_ = lean_apply_6(v_inst_2113_, v___f_2119_, lean_box(0), lean_box(0), v_it_2115_, v___x_2121_, v___f_2120_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_first_x3f___boxed(lean_object* v_00_u03b1_2123_, lean_object* v_00_u03b2_2124_, lean_object* v_m_2125_, lean_object* v_inst_2126_, lean_object* v_inst_2127_, lean_object* v_inst_2128_, lean_object* v_inst_2129_, lean_object* v_it_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Std_IterM_Total_first_x3f(v_00_u03b1_2123_, v_00_u03b2_2124_, v_m_2125_, v_inst_2126_, v_inst_2127_, v_inst_2128_, v_inst_2129_, v_it_2130_);
lean_dec(v_inst_2127_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___redArg___lam__1(lean_object* v_toPure_2135_, lean_object* v_x_2136_, lean_object* v_x_2137_, uint8_t v_x_2138_){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = ((lean_object*)(l_Std_IterM_isEmpty___redArg___lam__1___closed__0));
v___x_2140_ = lean_apply_2(v_toPure_2135_, lean_box(0), v___x_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___redArg___lam__1___boxed(lean_object* v_toPure_2141_, lean_object* v_x_2142_, lean_object* v_x_2143_, lean_object* v_x_2144_){
_start:
{
uint8_t v_x_79__boxed_2145_; lean_object* v_res_2146_; 
v_x_79__boxed_2145_ = lean_unbox(v_x_2144_);
v_res_2146_ = l_Std_IterM_isEmpty___redArg___lam__1(v_toPure_2141_, v_x_2142_, v_x_2143_, v_x_79__boxed_2145_);
lean_dec(v_x_2142_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___redArg(lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_it_2149_){
_start:
{
lean_object* v_toApplicative_2150_; lean_object* v_toBind_2151_; lean_object* v_toPure_2152_; lean_object* v___f_2153_; lean_object* v___f_2154_; uint8_t v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v_toApplicative_2150_ = lean_ctor_get(v_inst_2147_, 0);
lean_inc_ref(v_toApplicative_2150_);
v_toBind_2151_ = lean_ctor_get(v_inst_2147_, 1);
lean_inc(v_toBind_2151_);
lean_dec_ref(v_inst_2147_);
v_toPure_2152_ = lean_ctor_get(v_toApplicative_2150_, 1);
lean_inc(v_toPure_2152_);
lean_dec_ref(v_toApplicative_2150_);
v___f_2153_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2153_, 0, v_toBind_2151_);
v___f_2154_ = lean_alloc_closure((void*)(l_Std_IterM_isEmpty___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2154_, 0, v_toPure_2152_);
v___x_2155_ = 1;
v___x_2156_ = lean_box(v___x_2155_);
v___x_2157_ = lean_apply_6(v_inst_2148_, v___f_2153_, lean_box(0), lean_box(0), v_it_2149_, v___x_2156_, v___f_2154_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty(lean_object* v_00_u03b1_2158_, lean_object* v_00_u03b2_2159_, lean_object* v_m_2160_, lean_object* v_inst_2161_, lean_object* v_inst_2162_, lean_object* v_inst_2163_, lean_object* v_it_2164_){
_start:
{
lean_object* v_toApplicative_2165_; lean_object* v_toBind_2166_; lean_object* v_toPure_2167_; lean_object* v___f_2168_; lean_object* v___f_2169_; uint8_t v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v_toApplicative_2165_ = lean_ctor_get(v_inst_2161_, 0);
lean_inc_ref(v_toApplicative_2165_);
v_toBind_2166_ = lean_ctor_get(v_inst_2161_, 1);
lean_inc(v_toBind_2166_);
lean_dec_ref(v_inst_2161_);
v_toPure_2167_ = lean_ctor_get(v_toApplicative_2165_, 1);
lean_inc(v_toPure_2167_);
lean_dec_ref(v_toApplicative_2165_);
v___f_2168_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2168_, 0, v_toBind_2166_);
v___f_2169_ = lean_alloc_closure((void*)(l_Std_IterM_isEmpty___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2169_, 0, v_toPure_2167_);
v___x_2170_ = 1;
v___x_2171_ = lean_box(v___x_2170_);
v___x_2172_ = lean_apply_6(v_inst_2163_, v___f_2168_, lean_box(0), lean_box(0), v_it_2164_, v___x_2171_, v___f_2169_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___boxed(lean_object* v_00_u03b1_2173_, lean_object* v_00_u03b2_2174_, lean_object* v_m_2175_, lean_object* v_inst_2176_, lean_object* v_inst_2177_, lean_object* v_inst_2178_, lean_object* v_it_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Std_IterM_isEmpty(v_00_u03b1_2173_, v_00_u03b2_2174_, v_m_2175_, v_inst_2176_, v_inst_2177_, v_inst_2178_, v_it_2179_);
lean_dec(v_inst_2177_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_isEmpty___redArg(lean_object* v_inst_2181_, lean_object* v_inst_2182_, lean_object* v_it_2183_){
_start:
{
lean_object* v_toApplicative_2184_; lean_object* v_toBind_2185_; lean_object* v_toPure_2186_; lean_object* v___f_2187_; lean_object* v___f_2188_; uint8_t v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v_toApplicative_2184_ = lean_ctor_get(v_inst_2181_, 0);
lean_inc_ref(v_toApplicative_2184_);
v_toBind_2185_ = lean_ctor_get(v_inst_2181_, 1);
lean_inc(v_toBind_2185_);
lean_dec_ref(v_inst_2181_);
v_toPure_2186_ = lean_ctor_get(v_toApplicative_2184_, 1);
lean_inc(v_toPure_2186_);
lean_dec_ref(v_toApplicative_2184_);
v___f_2187_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2187_, 0, v_toBind_2185_);
v___f_2188_ = lean_alloc_closure((void*)(l_Std_IterM_isEmpty___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2188_, 0, v_toPure_2186_);
v___x_2189_ = 1;
v___x_2190_ = lean_box(v___x_2189_);
v___x_2191_ = lean_apply_6(v_inst_2182_, v___f_2187_, lean_box(0), lean_box(0), v_it_2183_, v___x_2190_, v___f_2188_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_isEmpty(lean_object* v_00_u03b1_2192_, lean_object* v_00_u03b2_2193_, lean_object* v_m_2194_, lean_object* v_inst_2195_, lean_object* v_inst_2196_, lean_object* v_inst_2197_, lean_object* v_inst_2198_, lean_object* v_it_2199_){
_start:
{
lean_object* v_toApplicative_2200_; lean_object* v_toBind_2201_; lean_object* v_toPure_2202_; lean_object* v___f_2203_; lean_object* v___f_2204_; uint8_t v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v_toApplicative_2200_ = lean_ctor_get(v_inst_2195_, 0);
lean_inc_ref(v_toApplicative_2200_);
v_toBind_2201_ = lean_ctor_get(v_inst_2195_, 1);
lean_inc(v_toBind_2201_);
lean_dec_ref(v_inst_2195_);
v_toPure_2202_ = lean_ctor_get(v_toApplicative_2200_, 1);
lean_inc(v_toPure_2202_);
lean_dec_ref(v_toApplicative_2200_);
v___f_2203_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2203_, 0, v_toBind_2201_);
v___f_2204_ = lean_alloc_closure((void*)(l_Std_IterM_isEmpty___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2204_, 0, v_toPure_2202_);
v___x_2205_ = 1;
v___x_2206_ = lean_box(v___x_2205_);
v___x_2207_ = lean_apply_6(v_inst_2197_, v___f_2203_, lean_box(0), lean_box(0), v_it_2199_, v___x_2206_, v___f_2204_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_isEmpty___boxed(lean_object* v_00_u03b1_2208_, lean_object* v_00_u03b2_2209_, lean_object* v_m_2210_, lean_object* v_inst_2211_, lean_object* v_inst_2212_, lean_object* v_inst_2213_, lean_object* v_inst_2214_, lean_object* v_it_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Std_IterM_Total_isEmpty(v_00_u03b1_2208_, v_00_u03b2_2209_, v_m_2210_, v_inst_2211_, v_inst_2212_, v_inst_2213_, v_inst_2214_, v_it_2215_);
lean_dec(v_inst_2212_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg___lam__1(lean_object* v_toPure_2217_, lean_object* v_____do__lift_2218_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = lean_apply_2(v_toPure_2217_, lean_box(0), v_____do__lift_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg___lam__0(lean_object* v_toPure_2220_, lean_object* v_toBind_2221_, lean_object* v___f_2222_, lean_object* v_x1_2223_, lean_object* v_x2_2224_, lean_object* v_x3_2225_){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2226_ = lean_unsigned_to_nat(1u);
v___x_2227_ = lean_nat_add(v_x3_2225_, v___x_2226_);
v___x_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
v___x_2229_ = lean_apply_2(v_toPure_2220_, lean_box(0), v___x_2228_);
v___x_2230_ = lean_apply_4(v_toBind_2221_, lean_box(0), lean_box(0), v___x_2229_, v___f_2222_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg___lam__0___boxed(lean_object* v_toPure_2231_, lean_object* v_toBind_2232_, lean_object* v___f_2233_, lean_object* v_x1_2234_, lean_object* v_x2_2235_, lean_object* v_x3_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Std_IterM_length___redArg___lam__0(v_toPure_2231_, v_toBind_2232_, v___f_2233_, v_x1_2234_, v_x2_2235_, v_x3_2236_);
lean_dec(v_x3_2236_);
lean_dec(v_x1_2234_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg(lean_object* v_inst_2238_, lean_object* v_inst_2239_, lean_object* v_it_2240_){
_start:
{
lean_object* v_toApplicative_2241_; lean_object* v_toBind_2242_; lean_object* v_toPure_2243_; lean_object* v___x_2244_; lean_object* v___f_2245_; lean_object* v___f_2246_; lean_object* v___f_2247_; lean_object* v___x_2248_; 
v_toApplicative_2241_ = lean_ctor_get(v_inst_2239_, 0);
lean_inc_ref(v_toApplicative_2241_);
v_toBind_2242_ = lean_ctor_get(v_inst_2239_, 1);
lean_inc(v_toBind_2242_);
lean_dec_ref(v_inst_2239_);
v_toPure_2243_ = lean_ctor_get(v_toApplicative_2241_, 1);
lean_inc(v_toPure_2243_);
lean_dec_ref(v_toApplicative_2241_);
v___x_2244_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2242_);
v___f_2245_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2245_, 0, v_toBind_2242_);
lean_inc(v_toPure_2243_);
v___f_2246_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2246_, 0, v_toPure_2243_);
v___f_2247_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2247_, 0, v_toPure_2243_);
lean_closure_set(v___f_2247_, 1, v_toBind_2242_);
lean_closure_set(v___f_2247_, 2, v___f_2246_);
v___x_2248_ = lean_apply_6(v_inst_2238_, v___f_2245_, lean_box(0), lean_box(0), v_it_2240_, v___x_2244_, v___f_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length(lean_object* v_00_u03b1_2249_, lean_object* v_m_2250_, lean_object* v_00_u03b2_2251_, lean_object* v_inst_2252_, lean_object* v_inst_2253_, lean_object* v_inst_2254_, lean_object* v_it_2255_){
_start:
{
lean_object* v_toApplicative_2256_; lean_object* v_toBind_2257_; lean_object* v_toPure_2258_; lean_object* v___x_2259_; lean_object* v___f_2260_; lean_object* v___f_2261_; lean_object* v___f_2262_; lean_object* v___x_2263_; 
v_toApplicative_2256_ = lean_ctor_get(v_inst_2254_, 0);
lean_inc_ref(v_toApplicative_2256_);
v_toBind_2257_ = lean_ctor_get(v_inst_2254_, 1);
lean_inc(v_toBind_2257_);
lean_dec_ref(v_inst_2254_);
v_toPure_2258_ = lean_ctor_get(v_toApplicative_2256_, 1);
lean_inc(v_toPure_2258_);
lean_dec_ref(v_toApplicative_2256_);
v___x_2259_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2257_);
v___f_2260_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2260_, 0, v_toBind_2257_);
lean_inc(v_toPure_2258_);
v___f_2261_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2261_, 0, v_toPure_2258_);
v___f_2262_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2262_, 0, v_toPure_2258_);
lean_closure_set(v___f_2262_, 1, v_toBind_2257_);
lean_closure_set(v___f_2262_, 2, v___f_2261_);
v___x_2263_ = lean_apply_6(v_inst_2253_, v___f_2260_, lean_box(0), lean_box(0), v_it_2255_, v___x_2259_, v___f_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___boxed(lean_object* v_00_u03b1_2264_, lean_object* v_m_2265_, lean_object* v_00_u03b2_2266_, lean_object* v_inst_2267_, lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v_it_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Std_IterM_length(v_00_u03b1_2264_, v_m_2265_, v_00_u03b2_2266_, v_inst_2267_, v_inst_2268_, v_inst_2269_, v_it_2270_);
lean_dec(v_inst_2267_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_count___redArg(lean_object* v_inst_2272_, lean_object* v_inst_2273_, lean_object* v_it_2274_){
_start:
{
lean_object* v_toApplicative_2275_; lean_object* v_toBind_2276_; lean_object* v_toPure_2277_; lean_object* v___x_2278_; lean_object* v___f_2279_; lean_object* v___f_2280_; lean_object* v___f_2281_; lean_object* v___x_2282_; 
v_toApplicative_2275_ = lean_ctor_get(v_inst_2273_, 0);
lean_inc_ref(v_toApplicative_2275_);
v_toBind_2276_ = lean_ctor_get(v_inst_2273_, 1);
lean_inc(v_toBind_2276_);
lean_dec_ref(v_inst_2273_);
v_toPure_2277_ = lean_ctor_get(v_toApplicative_2275_, 1);
lean_inc(v_toPure_2277_);
lean_dec_ref(v_toApplicative_2275_);
v___x_2278_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2276_);
v___f_2279_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2279_, 0, v_toBind_2276_);
lean_inc(v_toPure_2277_);
v___f_2280_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2280_, 0, v_toPure_2277_);
v___f_2281_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2281_, 0, v_toPure_2277_);
lean_closure_set(v___f_2281_, 1, v_toBind_2276_);
lean_closure_set(v___f_2281_, 2, v___f_2280_);
v___x_2282_ = lean_apply_6(v_inst_2272_, v___f_2279_, lean_box(0), lean_box(0), v_it_2274_, v___x_2278_, v___f_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_count(lean_object* v_00_u03b1_2283_, lean_object* v_m_2284_, lean_object* v_00_u03b2_2285_, lean_object* v_inst_2286_, lean_object* v_inst_2287_, lean_object* v_inst_2288_, lean_object* v_it_2289_){
_start:
{
lean_object* v_toApplicative_2290_; lean_object* v_toBind_2291_; lean_object* v_toPure_2292_; lean_object* v___x_2293_; lean_object* v___f_2294_; lean_object* v___f_2295_; lean_object* v___f_2296_; lean_object* v___x_2297_; 
v_toApplicative_2290_ = lean_ctor_get(v_inst_2288_, 0);
lean_inc_ref(v_toApplicative_2290_);
v_toBind_2291_ = lean_ctor_get(v_inst_2288_, 1);
lean_inc(v_toBind_2291_);
lean_dec_ref(v_inst_2288_);
v_toPure_2292_ = lean_ctor_get(v_toApplicative_2290_, 1);
lean_inc(v_toPure_2292_);
lean_dec_ref(v_toApplicative_2290_);
v___x_2293_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2291_);
v___f_2294_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2294_, 0, v_toBind_2291_);
lean_inc(v_toPure_2292_);
v___f_2295_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2295_, 0, v_toPure_2292_);
v___f_2296_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2296_, 0, v_toPure_2292_);
lean_closure_set(v___f_2296_, 1, v_toBind_2291_);
lean_closure_set(v___f_2296_, 2, v___f_2295_);
v___x_2297_ = lean_apply_6(v_inst_2287_, v___f_2294_, lean_box(0), lean_box(0), v_it_2289_, v___x_2293_, v___f_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_count___boxed(lean_object* v_00_u03b1_2298_, lean_object* v_m_2299_, lean_object* v_00_u03b2_2300_, lean_object* v_inst_2301_, lean_object* v_inst_2302_, lean_object* v_inst_2303_, lean_object* v_it_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Std_IterM_count(v_00_u03b1_2298_, v_m_2299_, v_00_u03b2_2300_, v_inst_2301_, v_inst_2302_, v_inst_2303_, v_it_2304_);
lean_dec(v_inst_2301_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_size___redArg(lean_object* v_inst_2306_, lean_object* v_inst_2307_, lean_object* v_it_2308_){
_start:
{
lean_object* v_toApplicative_2309_; lean_object* v_toBind_2310_; lean_object* v_toPure_2311_; lean_object* v___x_2312_; lean_object* v___f_2313_; lean_object* v___f_2314_; lean_object* v___f_2315_; lean_object* v___x_2316_; 
v_toApplicative_2309_ = lean_ctor_get(v_inst_2307_, 0);
lean_inc_ref(v_toApplicative_2309_);
v_toBind_2310_ = lean_ctor_get(v_inst_2307_, 1);
lean_inc(v_toBind_2310_);
lean_dec_ref(v_inst_2307_);
v_toPure_2311_ = lean_ctor_get(v_toApplicative_2309_, 1);
lean_inc(v_toPure_2311_);
lean_dec_ref(v_toApplicative_2309_);
v___x_2312_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2310_);
v___f_2313_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2313_, 0, v_toBind_2310_);
lean_inc(v_toPure_2311_);
v___f_2314_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2314_, 0, v_toPure_2311_);
v___f_2315_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2315_, 0, v_toPure_2311_);
lean_closure_set(v___f_2315_, 1, v_toBind_2310_);
lean_closure_set(v___f_2315_, 2, v___f_2314_);
v___x_2316_ = lean_apply_6(v_inst_2306_, v___f_2313_, lean_box(0), lean_box(0), v_it_2308_, v___x_2312_, v___f_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_size(lean_object* v_00_u03b1_2317_, lean_object* v_m_2318_, lean_object* v_00_u03b2_2319_, lean_object* v_inst_2320_, lean_object* v_inst_2321_, lean_object* v_inst_2322_, lean_object* v_it_2323_){
_start:
{
lean_object* v_toApplicative_2324_; lean_object* v_toBind_2325_; lean_object* v_toPure_2326_; lean_object* v___x_2327_; lean_object* v___f_2328_; lean_object* v___f_2329_; lean_object* v___f_2330_; lean_object* v___x_2331_; 
v_toApplicative_2324_ = lean_ctor_get(v_inst_2322_, 0);
lean_inc_ref(v_toApplicative_2324_);
v_toBind_2325_ = lean_ctor_get(v_inst_2322_, 1);
lean_inc(v_toBind_2325_);
lean_dec_ref(v_inst_2322_);
v_toPure_2326_ = lean_ctor_get(v_toApplicative_2324_, 1);
lean_inc(v_toPure_2326_);
lean_dec_ref(v_toApplicative_2324_);
v___x_2327_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2325_);
v___f_2328_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2328_, 0, v_toBind_2325_);
lean_inc(v_toPure_2326_);
v___f_2329_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2329_, 0, v_toPure_2326_);
v___f_2330_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2330_, 0, v_toPure_2326_);
lean_closure_set(v___f_2330_, 1, v_toBind_2325_);
lean_closure_set(v___f_2330_, 2, v___f_2329_);
v___x_2331_ = lean_apply_6(v_inst_2321_, v___f_2328_, lean_box(0), lean_box(0), v_it_2323_, v___x_2327_, v___f_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_size___boxed(lean_object* v_00_u03b1_2332_, lean_object* v_m_2333_, lean_object* v_00_u03b2_2334_, lean_object* v_inst_2335_, lean_object* v_inst_2336_, lean_object* v_inst_2337_, lean_object* v_it_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Std_IterM_size(v_00_u03b1_2332_, v_m_2333_, v_00_u03b2_2334_, v_inst_2335_, v_inst_2336_, v_inst_2337_, v_it_2338_);
lean_dec(v_inst_2335_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count___redArg(lean_object* v_inst_2340_, lean_object* v_inst_2341_, lean_object* v_it_2342_){
_start:
{
lean_object* v_toApplicative_2343_; lean_object* v_toBind_2344_; lean_object* v_toPure_2345_; lean_object* v___x_2346_; lean_object* v___f_2347_; lean_object* v___f_2348_; lean_object* v___f_2349_; lean_object* v___x_2350_; 
v_toApplicative_2343_ = lean_ctor_get(v_inst_2341_, 0);
lean_inc_ref(v_toApplicative_2343_);
v_toBind_2344_ = lean_ctor_get(v_inst_2341_, 1);
lean_inc(v_toBind_2344_);
lean_dec_ref(v_inst_2341_);
v_toPure_2345_ = lean_ctor_get(v_toApplicative_2343_, 1);
lean_inc(v_toPure_2345_);
lean_dec_ref(v_toApplicative_2343_);
v___x_2346_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2344_);
v___f_2347_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2347_, 0, v_toBind_2344_);
lean_inc(v_toPure_2345_);
v___f_2348_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2348_, 0, v_toPure_2345_);
v___f_2349_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2349_, 0, v_toPure_2345_);
lean_closure_set(v___f_2349_, 1, v_toBind_2344_);
lean_closure_set(v___f_2349_, 2, v___f_2348_);
v___x_2350_ = lean_apply_6(v_inst_2340_, v___f_2347_, lean_box(0), lean_box(0), v_it_2342_, v___x_2346_, v___f_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count(lean_object* v_00_u03b1_2351_, lean_object* v_m_2352_, lean_object* v_00_u03b2_2353_, lean_object* v_inst_2354_, lean_object* v_inst_2355_, lean_object* v_inst_2356_, lean_object* v_it_2357_){
_start:
{
lean_object* v_toApplicative_2358_; lean_object* v_toBind_2359_; lean_object* v_toPure_2360_; lean_object* v___x_2361_; lean_object* v___f_2362_; lean_object* v___f_2363_; lean_object* v___f_2364_; lean_object* v___x_2365_; 
v_toApplicative_2358_ = lean_ctor_get(v_inst_2356_, 0);
lean_inc_ref(v_toApplicative_2358_);
v_toBind_2359_ = lean_ctor_get(v_inst_2356_, 1);
lean_inc(v_toBind_2359_);
lean_dec_ref(v_inst_2356_);
v_toPure_2360_ = lean_ctor_get(v_toApplicative_2358_, 1);
lean_inc(v_toPure_2360_);
lean_dec_ref(v_toApplicative_2358_);
v___x_2361_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2359_);
v___f_2362_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2362_, 0, v_toBind_2359_);
lean_inc(v_toPure_2360_);
v___f_2363_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2363_, 0, v_toPure_2360_);
v___f_2364_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2364_, 0, v_toPure_2360_);
lean_closure_set(v___f_2364_, 1, v_toBind_2359_);
lean_closure_set(v___f_2364_, 2, v___f_2363_);
v___x_2365_ = lean_apply_6(v_inst_2355_, v___f_2362_, lean_box(0), lean_box(0), v_it_2357_, v___x_2361_, v___f_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count___boxed(lean_object* v_00_u03b1_2366_, lean_object* v_m_2367_, lean_object* v_00_u03b2_2368_, lean_object* v_inst_2369_, lean_object* v_inst_2370_, lean_object* v_inst_2371_, lean_object* v_it_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Std_IterM_Partial_count(v_00_u03b1_2366_, v_m_2367_, v_00_u03b2_2368_, v_inst_2369_, v_inst_2370_, v_inst_2371_, v_it_2372_);
lean_dec(v_inst_2369_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size___redArg(lean_object* v_inst_2374_, lean_object* v_inst_2375_, lean_object* v_it_2376_){
_start:
{
lean_object* v_toApplicative_2377_; lean_object* v_toBind_2378_; lean_object* v_toPure_2379_; lean_object* v___x_2380_; lean_object* v___f_2381_; lean_object* v___f_2382_; lean_object* v___f_2383_; lean_object* v___x_2384_; 
v_toApplicative_2377_ = lean_ctor_get(v_inst_2375_, 0);
lean_inc_ref(v_toApplicative_2377_);
v_toBind_2378_ = lean_ctor_get(v_inst_2375_, 1);
lean_inc(v_toBind_2378_);
lean_dec_ref(v_inst_2375_);
v_toPure_2379_ = lean_ctor_get(v_toApplicative_2377_, 1);
lean_inc(v_toPure_2379_);
lean_dec_ref(v_toApplicative_2377_);
v___x_2380_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2378_);
v___f_2381_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2381_, 0, v_toBind_2378_);
lean_inc(v_toPure_2379_);
v___f_2382_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2382_, 0, v_toPure_2379_);
v___f_2383_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2383_, 0, v_toPure_2379_);
lean_closure_set(v___f_2383_, 1, v_toBind_2378_);
lean_closure_set(v___f_2383_, 2, v___f_2382_);
v___x_2384_ = lean_apply_6(v_inst_2374_, v___f_2381_, lean_box(0), lean_box(0), v_it_2376_, v___x_2380_, v___f_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size(lean_object* v_00_u03b1_2385_, lean_object* v_m_2386_, lean_object* v_00_u03b2_2387_, lean_object* v_inst_2388_, lean_object* v_inst_2389_, lean_object* v_inst_2390_, lean_object* v_it_2391_){
_start:
{
lean_object* v_toApplicative_2392_; lean_object* v_toBind_2393_; lean_object* v_toPure_2394_; lean_object* v___x_2395_; lean_object* v___f_2396_; lean_object* v___f_2397_; lean_object* v___f_2398_; lean_object* v___x_2399_; 
v_toApplicative_2392_ = lean_ctor_get(v_inst_2390_, 0);
lean_inc_ref(v_toApplicative_2392_);
v_toBind_2393_ = lean_ctor_get(v_inst_2390_, 1);
lean_inc(v_toBind_2393_);
lean_dec_ref(v_inst_2390_);
v_toPure_2394_ = lean_ctor_get(v_toApplicative_2392_, 1);
lean_inc(v_toPure_2394_);
lean_dec_ref(v_toApplicative_2392_);
v___x_2395_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2393_);
v___f_2396_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2396_, 0, v_toBind_2393_);
lean_inc(v_toPure_2394_);
v___f_2397_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2397_, 0, v_toPure_2394_);
v___f_2398_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2398_, 0, v_toPure_2394_);
lean_closure_set(v___f_2398_, 1, v_toBind_2393_);
lean_closure_set(v___f_2398_, 2, v___f_2397_);
v___x_2399_ = lean_apply_6(v_inst_2389_, v___f_2396_, lean_box(0), lean_box(0), v_it_2391_, v___x_2395_, v___f_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size___boxed(lean_object* v_00_u03b1_2400_, lean_object* v_m_2401_, lean_object* v_00_u03b2_2402_, lean_object* v_inst_2403_, lean_object* v_inst_2404_, lean_object* v_inst_2405_, lean_object* v_it_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Std_IterM_Partial_size(v_00_u03b1_2400_, v_m_2401_, v_00_u03b2_2402_, v_inst_2403_, v_inst_2404_, v_inst_2405_, v_it_2406_);
lean_dec(v_inst_2403_);
return v_res_2407_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Partial(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(uint8_t builtin);
lean_object* runtime_initialize_Init_WFExtrinsicFix(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Partial(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFExtrinsicFix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Partial(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(uint8_t builtin);
lean_object* initialize_Init_WFExtrinsicFix(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Total(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
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
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
}
#ifdef __cplusplus
}
#endif
