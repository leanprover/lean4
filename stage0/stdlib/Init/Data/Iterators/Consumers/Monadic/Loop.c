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
lean_object* v___x_156_; 
v___x_156_ = l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(v_x_152_, v_h__1_153_, v_h__2_154_, v_h__3_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(lean_object* v_m_157_, lean_object* v_00_u03b1_158_, lean_object* v_00_u03b2_159_, lean_object* v_inst_160_, lean_object* v_it_161_, lean_object* v_motive_162_, lean_object* v_x_163_, lean_object* v_h__1_164_, lean_object* v_h__2_165_, lean_object* v_h__3_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(v_m_157_, v_00_u03b1_158_, v_00_u03b2_159_, v_inst_160_, v_it_161_, v_motive_162_, v_x_163_, v_h__1_164_, v_h__2_165_, v_h__3_166_);
lean_dec(v_it_161_);
lean_dec(v_inst_160_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(lean_object* v_____do__lift_168_, lean_object* v_h__1_169_, lean_object* v_h__2_170_){
_start:
{
if (lean_obj_tag(v_____do__lift_168_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_172_; 
lean_dec(v_h__1_169_);
v_a_171_ = lean_ctor_get(v_____do__lift_168_, 0);
lean_inc(v_a_171_);
lean_dec_ref(v_____do__lift_168_);
v___x_172_ = lean_apply_2(v_h__2_170_, v_a_171_, lean_box(0));
return v___x_172_;
}
else
{
lean_object* v_a_173_; lean_object* v___x_174_; 
lean_dec(v_h__2_170_);
v_a_173_ = lean_ctor_get(v_____do__lift_168_, 0);
lean_inc(v_a_173_);
lean_dec_ref(v_____do__lift_168_);
v___x_174_ = lean_apply_2(v_h__1_169_, v_a_173_, lean_box(0));
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(lean_object* v_00_u03b2_175_, lean_object* v_00_u03b3_176_, lean_object* v_PlausibleForInStep_177_, lean_object* v_acc_178_, lean_object* v_out_179_, lean_object* v_motive_180_, lean_object* v_____do__lift_181_, lean_object* v_h__1_182_, lean_object* v_h__2_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(v_____do__lift_181_, v_h__1_182_, v_h__2_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(lean_object* v_00_u03b2_185_, lean_object* v_00_u03b3_186_, lean_object* v_PlausibleForInStep_187_, lean_object* v_acc_188_, lean_object* v_out_189_, lean_object* v_motive_190_, lean_object* v_____do__lift_191_, lean_object* v_h__1_192_, lean_object* v_h__2_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(v_00_u03b2_185_, v_00_u03b3_186_, v_PlausibleForInStep_187_, v_acc_188_, v_out_189_, v_motive_190_, v_____do__lift_191_, v_h__1_192_, v_h__2_193_);
lean_dec(v_out_189_);
lean_dec(v_acc_188_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__1(lean_object* v_toPure_195_, lean_object* v_recur_196_, lean_object* v___y_197_, lean_object* v_acc_198_, lean_object* v_toBind_199_, lean_object* v_s_200_){
_start:
{
switch(lean_obj_tag(v_s_200_))
{
case 0:
{
lean_object* v_it_201_; lean_object* v_out_202_; lean_object* v___f_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_it_201_ = lean_ctor_get(v_s_200_, 0);
lean_inc(v_it_201_);
v_out_202_ = lean_ctor_get(v_s_200_, 1);
lean_inc(v_out_202_);
lean_dec_ref(v_s_200_);
v___f_203_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_203_, 0, v_toPure_195_);
lean_closure_set(v___f_203_, 1, v_recur_196_);
lean_closure_set(v___f_203_, 2, v_it_201_);
v___x_204_ = lean_apply_3(v___y_197_, v_out_202_, lean_box(0), v_acc_198_);
v___x_205_ = lean_apply_4(v_toBind_199_, lean_box(0), lean_box(0), v___x_204_, v___f_203_);
return v___x_205_;
}
case 1:
{
lean_object* v_it_206_; lean_object* v___x_207_; 
lean_dec(v_toBind_199_);
lean_dec(v___y_197_);
lean_dec(v_toPure_195_);
v_it_206_ = lean_ctor_get(v_s_200_, 0);
lean_inc(v_it_206_);
lean_dec_ref(v_s_200_);
v___x_207_ = lean_apply_4(v_recur_196_, v_it_206_, v_acc_198_, lean_box(0), lean_box(0));
return v___x_207_;
}
default: 
{
lean_object* v___x_208_; 
lean_dec(v_toBind_199_);
lean_dec(v___y_197_);
lean_dec(v_recur_196_);
v___x_208_ = lean_apply_2(v_toPure_195_, lean_box(0), v_acc_198_);
return v___x_208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__0(lean_object* v_toPure_209_, lean_object* v___y_210_, lean_object* v_toBind_211_, lean_object* v_inst_212_, lean_object* v_lift_213_, lean_object* v_it_214_, lean_object* v_acc_215_, lean_object* v_hP_216_, lean_object* v_recur_217_){
_start:
{
lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___f_218_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__1), 6, 5);
lean_closure_set(v___f_218_, 0, v_toPure_209_);
lean_closure_set(v___f_218_, 1, v_recur_217_);
lean_closure_set(v___f_218_, 2, v___y_210_);
lean_closure_set(v___f_218_, 3, v_acc_215_);
lean_closure_set(v___f_218_, 4, v_toBind_211_);
v___x_219_ = lean_apply_1(v_inst_212_, v_it_214_);
v___x_220_ = lean_apply_4(v_lift_213_, lean_box(0), lean_box(0), v___f_218_, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__2(lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_lift_223_, lean_object* v_00_u03b3_224_, lean_object* v_Pl_225_, lean_object* v_it_226_, lean_object* v_init_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_toApplicative_229_; lean_object* v_toBind_230_; lean_object* v_toPure_231_; lean_object* v___f_232_; lean_object* v___x_233_; 
v_toApplicative_229_ = lean_ctor_get(v_inst_221_, 0);
lean_inc_ref(v_toApplicative_229_);
v_toBind_230_ = lean_ctor_get(v_inst_221_, 1);
lean_inc(v_toBind_230_);
lean_dec_ref(v_inst_221_);
v_toPure_231_ = lean_ctor_get(v_toApplicative_229_, 1);
lean_inc(v_toPure_231_);
lean_dec_ref(v_toApplicative_229_);
v___f_232_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__0), 9, 5);
lean_closure_set(v___f_232_, 0, v_toPure_231_);
lean_closure_set(v___f_232_, 1, v___y_228_);
lean_closure_set(v___f_232_, 2, v_toBind_230_);
lean_closure_set(v___f_232_, 3, v_inst_222_);
lean_closure_set(v___f_232_, 4, v_lift_223_);
v___x_233_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_232_, v_it_226_, v_init_227_, lean_box(0));
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg(lean_object* v_inst_234_, lean_object* v_inst_235_){
_start:
{
lean_object* v___f_236_; 
v___f_236_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__2), 8, 2);
lean_closure_set(v___f_236_, 0, v_inst_234_);
lean_closure_set(v___f_236_, 1, v_inst_235_);
return v___f_236_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation(lean_object* v_00_u03b2_237_, lean_object* v_00_u03b1_238_, lean_object* v_m_239_, lean_object* v_n_240_, lean_object* v_inst_241_, lean_object* v_inst_242_){
_start:
{
lean_object* v___f_243_; 
v___f_243_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__2), 8, 2);
lean_closure_set(v___f_243_, 0, v_inst_241_);
lean_closure_set(v___f_243_, 1, v_inst_242_);
return v___f_243_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0(lean_object* v_toPure_244_, lean_object* v_____do__lift_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_apply_2(v_toPure_244_, lean_box(0), v_____do__lift_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1(lean_object* v_f_247_, lean_object* v_toBind_248_, lean_object* v___f_249_, lean_object* v_x1_250_, lean_object* v_x2_251_, lean_object* v_x3_252_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_apply_3(v_f_247_, v_x1_250_, lean_box(0), v_x3_252_);
v___x_254_ = lean_apply_4(v_toBind_248_, lean_box(0), lean_box(0), v___x_253_, v___f_249_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2(lean_object* v_toBind_255_, lean_object* v___f_256_, lean_object* v_inst_257_, lean_object* v_lift_258_, lean_object* v_00_u03b3_259_, lean_object* v_it_260_, lean_object* v_init_261_, lean_object* v_f_262_){
_start:
{
lean_object* v___f_263_; lean_object* v___x_264_; 
v___f_263_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1), 6, 3);
lean_closure_set(v___f_263_, 0, v_f_262_);
lean_closure_set(v___f_263_, 1, v_toBind_255_);
lean_closure_set(v___f_263_, 2, v___f_256_);
v___x_264_ = lean_apply_6(v_inst_257_, v_lift_258_, lean_box(0), lean_box(0), v_it_260_, v_init_261_, v___f_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg(lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_lift_267_){
_start:
{
lean_object* v_toApplicative_268_; lean_object* v_toBind_269_; lean_object* v_toPure_270_; lean_object* v___f_271_; lean_object* v___f_272_; 
v_toApplicative_268_ = lean_ctor_get(v_inst_266_, 0);
lean_inc_ref(v_toApplicative_268_);
v_toBind_269_ = lean_ctor_get(v_inst_266_, 1);
lean_inc(v_toBind_269_);
lean_dec_ref(v_inst_266_);
v_toPure_270_ = lean_ctor_get(v_toApplicative_268_, 1);
lean_inc(v_toPure_270_);
lean_dec_ref(v_toApplicative_268_);
v___f_271_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_271_, 0, v_toPure_270_);
v___f_272_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2), 8, 4);
lean_closure_set(v___f_272_, 0, v_toBind_269_);
lean_closure_set(v___f_272_, 1, v___f_271_);
lean_closure_set(v___f_272_, 2, v_inst_265_);
lean_closure_set(v___f_272_, 3, v_lift_267_);
return v___f_272_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27(lean_object* v_m_273_, lean_object* v_n_274_, lean_object* v_00_u03b1_275_, lean_object* v_00_u03b2_276_, lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_lift_280_){
_start:
{
lean_object* v_toApplicative_281_; lean_object* v_toBind_282_; lean_object* v_toPure_283_; lean_object* v___f_284_; lean_object* v___f_285_; 
v_toApplicative_281_ = lean_ctor_get(v_inst_279_, 0);
lean_inc_ref(v_toApplicative_281_);
v_toBind_282_ = lean_ctor_get(v_inst_279_, 1);
lean_inc(v_toBind_282_);
lean_dec_ref(v_inst_279_);
v_toPure_283_ = lean_ctor_get(v_toApplicative_281_, 1);
lean_inc(v_toPure_283_);
lean_dec_ref(v_toApplicative_281_);
v___f_284_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_284_, 0, v_toPure_283_);
v___f_285_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2), 8, 4);
lean_closure_set(v___f_285_, 0, v_toBind_282_);
lean_closure_set(v___f_285_, 1, v___f_284_);
lean_closure_set(v___f_285_, 2, v_inst_278_);
lean_closure_set(v___f_285_, 3, v_lift_280_);
return v___f_285_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___boxed(lean_object* v_m_286_, lean_object* v_n_287_, lean_object* v_00_u03b1_288_, lean_object* v_00_u03b2_289_, lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_lift_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Std_IteratorLoop_finiteForIn_x27(v_m_286_, v_n_287_, v_00_u03b1_288_, v_00_u03b2_289_, v_inst_290_, v_inst_291_, v_inst_292_, v_lift_293_);
lean_dec(v_inst_290_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg___lam__0(lean_object* v_inst_295_, lean_object* v_toBind_296_, lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v_f_299_, lean_object* v_x_300_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_apply_2(v_inst_295_, lean_box(0), v_x_300_);
v___x_302_ = lean_apply_4(v_toBind_296_, lean_box(0), lean_box(0), v___x_301_, v_f_299_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg___lam__3(lean_object* v_toBind_303_, lean_object* v___f_304_, lean_object* v_inst_305_, lean_object* v___f_306_, lean_object* v_00_u03b3_307_, lean_object* v_it_308_, lean_object* v_init_309_, lean_object* v_f_310_){
_start:
{
lean_object* v___f_311_; lean_object* v___x_312_; 
v___f_311_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1), 6, 3);
lean_closure_set(v___f_311_, 0, v_f_310_);
lean_closure_set(v___f_311_, 1, v_toBind_303_);
lean_closure_set(v___f_311_, 2, v___f_304_);
v___x_312_ = lean_apply_6(v_inst_305_, v___f_306_, lean_box(0), lean_box(0), v_it_308_, v_init_309_, v___f_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg(lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_inst_315_){
_start:
{
lean_object* v_toApplicative_316_; lean_object* v_toBind_317_; lean_object* v_toPure_318_; lean_object* v___f_319_; lean_object* v___f_320_; lean_object* v___f_321_; 
v_toApplicative_316_ = lean_ctor_get(v_inst_314_, 0);
lean_inc_ref(v_toApplicative_316_);
v_toBind_317_ = lean_ctor_get(v_inst_314_, 1);
lean_inc(v_toBind_317_);
lean_dec_ref(v_inst_314_);
v_toPure_318_ = lean_ctor_get(v_toApplicative_316_, 1);
lean_inc(v_toPure_318_);
lean_dec_ref(v_toApplicative_316_);
lean_inc(v_toBind_317_);
v___f_319_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_319_, 0, v_inst_315_);
lean_closure_set(v___f_319_, 1, v_toBind_317_);
v___f_320_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_320_, 0, v_toPure_318_);
v___f_321_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_321_, 0, v_toBind_317_);
lean_closure_set(v___f_321_, 1, v___f_320_);
lean_closure_set(v___f_321_, 2, v_inst_313_);
lean_closure_set(v___f_321_, 3, v___f_319_);
return v___f_321_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27(lean_object* v_m_322_, lean_object* v_n_323_, lean_object* v_00_u03b1_324_, lean_object* v_00_u03b2_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_inst_328_, lean_object* v_inst_329_){
_start:
{
lean_object* v_toApplicative_330_; lean_object* v_toBind_331_; lean_object* v_toPure_332_; lean_object* v___f_333_; lean_object* v___f_334_; lean_object* v___f_335_; 
v_toApplicative_330_ = lean_ctor_get(v_inst_328_, 0);
lean_inc_ref(v_toApplicative_330_);
v_toBind_331_ = lean_ctor_get(v_inst_328_, 1);
lean_inc(v_toBind_331_);
lean_dec_ref(v_inst_328_);
v_toPure_332_ = lean_ctor_get(v_toApplicative_330_, 1);
lean_inc(v_toPure_332_);
lean_dec_ref(v_toApplicative_330_);
lean_inc(v_toBind_331_);
v___f_333_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_333_, 0, v_inst_329_);
lean_closure_set(v___f_333_, 1, v_toBind_331_);
v___f_334_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_334_, 0, v_toPure_332_);
v___f_335_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_335_, 0, v_toBind_331_);
lean_closure_set(v___f_335_, 1, v___f_334_);
lean_closure_set(v___f_335_, 2, v_inst_327_);
lean_closure_set(v___f_335_, 3, v___f_333_);
return v___f_335_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___boxed(lean_object* v_m_336_, lean_object* v_n_337_, lean_object* v_00_u03b1_338_, lean_object* v_00_u03b2_339_, lean_object* v_inst_340_, lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_inst_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Std_IterM_instForIn_x27(v_m_336_, v_n_337_, v_00_u03b1_338_, v_00_u03b2_339_, v_inst_340_, v_inst_341_, v_inst_342_, v_inst_343_);
lean_dec(v_inst_340_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop___redArg(lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_inst_347_){
_start:
{
lean_object* v_toApplicative_348_; lean_object* v_toBind_349_; lean_object* v_toPure_350_; lean_object* v___f_351_; lean_object* v___f_352_; lean_object* v___f_353_; lean_object* v___f_354_; 
v_toApplicative_348_ = lean_ctor_get(v_inst_347_, 0);
lean_inc_ref(v_toApplicative_348_);
v_toBind_349_ = lean_ctor_get(v_inst_347_, 1);
lean_inc(v_toBind_349_);
lean_dec_ref(v_inst_347_);
v_toPure_350_ = lean_ctor_get(v_toApplicative_348_, 1);
lean_inc(v_toPure_350_);
lean_dec_ref(v_toApplicative_348_);
lean_inc(v_toBind_349_);
v___f_351_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_351_, 0, v_inst_346_);
lean_closure_set(v___f_351_, 1, v_toBind_349_);
v___f_352_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_352_, 0, v_toPure_350_);
v___f_353_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_353_, 0, v_toBind_349_);
lean_closure_set(v___f_353_, 1, v___f_352_);
lean_closure_set(v___f_353_, 2, v_inst_345_);
lean_closure_set(v___f_353_, 3, v___f_351_);
v___f_354_ = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(v___f_354_, 0, v___f_353_);
return v___f_354_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop(lean_object* v_m_355_, lean_object* v_n_356_, lean_object* v_00_u03b1_357_, lean_object* v_00_u03b2_358_, lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_inst_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Std_IterM_instForInOfIteratorLoop___redArg(v_inst_360_, v_inst_361_, v_inst_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop___boxed(lean_object* v_m_364_, lean_object* v_n_365_, lean_object* v_00_u03b1_366_, lean_object* v_00_u03b2_367_, lean_object* v_inst_368_, lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_inst_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Std_IterM_instForInOfIteratorLoop(v_m_364_, v_n_365_, v_00_u03b1_366_, v_00_u03b2_367_, v_inst_368_, v_inst_369_, v_inst_370_, v_inst_371_);
lean_dec(v_inst_368_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___redArg___lam__3(lean_object* v_toBind_373_, lean_object* v___f_374_, lean_object* v_inst_375_, lean_object* v___f_376_, lean_object* v_00_u03b2_377_, lean_object* v_it_378_, lean_object* v_init_379_, lean_object* v_f_380_){
_start:
{
lean_object* v___f_381_; lean_object* v___x_382_; 
v___f_381_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1), 6, 3);
lean_closure_set(v___f_381_, 0, v_f_380_);
lean_closure_set(v___f_381_, 1, v_toBind_373_);
lean_closure_set(v___f_381_, 2, v___f_374_);
v___x_382_ = lean_apply_6(v_inst_375_, v___f_376_, lean_box(0), lean_box(0), v_it_378_, v_init_379_, v___f_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___redArg(lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_inst_385_){
_start:
{
lean_object* v_toApplicative_386_; lean_object* v_toBind_387_; lean_object* v_toPure_388_; lean_object* v___f_389_; lean_object* v___f_390_; lean_object* v___f_391_; 
v_toApplicative_386_ = lean_ctor_get(v_inst_385_, 0);
lean_inc_ref(v_toApplicative_386_);
v_toBind_387_ = lean_ctor_get(v_inst_385_, 1);
lean_inc(v_toBind_387_);
lean_dec_ref(v_inst_385_);
v_toPure_388_ = lean_ctor_get(v_toApplicative_386_, 1);
lean_inc(v_toPure_388_);
lean_dec_ref(v_toApplicative_386_);
lean_inc(v_toBind_387_);
v___f_389_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_389_, 0, v_inst_384_);
lean_closure_set(v___f_389_, 1, v_toBind_387_);
v___f_390_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_390_, 0, v_toPure_388_);
v___f_391_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_391_, 0, v_toBind_387_);
lean_closure_set(v___f_391_, 1, v___f_390_);
lean_closure_set(v___f_391_, 2, v_inst_383_);
lean_closure_set(v___f_391_, 3, v___f_389_);
return v___f_391_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27(lean_object* v_m_392_, lean_object* v_n_393_, lean_object* v_00_u03b1_394_, lean_object* v_00_u03b2_395_, lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_inst_399_){
_start:
{
lean_object* v_toApplicative_400_; lean_object* v_toBind_401_; lean_object* v_toPure_402_; lean_object* v___f_403_; lean_object* v___f_404_; lean_object* v___f_405_; 
v_toApplicative_400_ = lean_ctor_get(v_inst_399_, 0);
lean_inc_ref(v_toApplicative_400_);
v_toBind_401_ = lean_ctor_get(v_inst_399_, 1);
lean_inc(v_toBind_401_);
lean_dec_ref(v_inst_399_);
v_toPure_402_ = lean_ctor_get(v_toApplicative_400_, 1);
lean_inc(v_toPure_402_);
lean_dec_ref(v_toApplicative_400_);
lean_inc(v_toBind_401_);
v___f_403_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_403_, 0, v_inst_398_);
lean_closure_set(v___f_403_, 1, v_toBind_401_);
v___f_404_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_404_, 0, v_toPure_402_);
v___f_405_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_405_, 0, v_toBind_401_);
lean_closure_set(v___f_405_, 1, v___f_404_);
lean_closure_set(v___f_405_, 2, v_inst_397_);
lean_closure_set(v___f_405_, 3, v___f_403_);
return v___f_405_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___boxed(lean_object* v_m_406_, lean_object* v_n_407_, lean_object* v_00_u03b1_408_, lean_object* v_00_u03b2_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_inst_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Std_IterM_Partial_instForIn_x27(v_m_406_, v_n_407_, v_00_u03b1_408_, v_00_u03b2_409_, v_inst_410_, v_inst_411_, v_inst_412_, v_inst_413_);
lean_dec(v_inst_410_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27___redArg(lean_object* v_inst_415_, lean_object* v_inst_416_, lean_object* v_inst_417_){
_start:
{
lean_object* v_toApplicative_418_; lean_object* v_toBind_419_; lean_object* v_toPure_420_; lean_object* v___f_421_; lean_object* v___f_422_; lean_object* v___f_423_; 
v_toApplicative_418_ = lean_ctor_get(v_inst_417_, 0);
lean_inc_ref(v_toApplicative_418_);
v_toBind_419_ = lean_ctor_get(v_inst_417_, 1);
lean_inc(v_toBind_419_);
lean_dec_ref(v_inst_417_);
v_toPure_420_ = lean_ctor_get(v_toApplicative_418_, 1);
lean_inc(v_toPure_420_);
lean_dec_ref(v_toApplicative_418_);
lean_inc(v_toBind_419_);
v___f_421_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_421_, 0, v_inst_416_);
lean_closure_set(v___f_421_, 1, v_toBind_419_);
v___f_422_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_422_, 0, v_toPure_420_);
v___f_423_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_423_, 0, v_toBind_419_);
lean_closure_set(v___f_423_, 1, v___f_422_);
lean_closure_set(v___f_423_, 2, v_inst_415_);
lean_closure_set(v___f_423_, 3, v___f_421_);
return v___f_423_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27(lean_object* v_m_424_, lean_object* v_n_425_, lean_object* v_00_u03b1_426_, lean_object* v_00_u03b2_427_, lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_inst_432_){
_start:
{
lean_object* v_toApplicative_433_; lean_object* v_toBind_434_; lean_object* v_toPure_435_; lean_object* v___f_436_; lean_object* v___f_437_; lean_object* v___f_438_; 
v_toApplicative_433_ = lean_ctor_get(v_inst_431_, 0);
lean_inc_ref(v_toApplicative_433_);
v_toBind_434_ = lean_ctor_get(v_inst_431_, 1);
lean_inc(v_toBind_434_);
lean_dec_ref(v_inst_431_);
v_toPure_435_ = lean_ctor_get(v_toApplicative_433_, 1);
lean_inc(v_toPure_435_);
lean_dec_ref(v_toApplicative_433_);
lean_inc(v_toBind_434_);
v___f_436_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_436_, 0, v_inst_430_);
lean_closure_set(v___f_436_, 1, v_toBind_434_);
v___f_437_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_437_, 0, v_toPure_435_);
v___f_438_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_438_, 0, v_toBind_434_);
lean_closure_set(v___f_438_, 1, v___f_437_);
lean_closure_set(v___f_438_, 2, v_inst_429_);
lean_closure_set(v___f_438_, 3, v___f_436_);
return v___f_438_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27___boxed(lean_object* v_m_439_, lean_object* v_n_440_, lean_object* v_00_u03b1_441_, lean_object* v_00_u03b2_442_, lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Std_IterM_Total_instForIn_x27(v_m_439_, v_n_440_, v_00_u03b1_441_, v_00_u03b2_442_, v_inst_443_, v_inst_444_, v_inst_445_, v_inst_446_, v_inst_447_);
lean_dec(v_inst_443_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop___redArg(lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_inst_451_){
_start:
{
lean_object* v_toApplicative_452_; lean_object* v_toBind_453_; lean_object* v_toPure_454_; lean_object* v___f_455_; lean_object* v___f_456_; lean_object* v___f_457_; lean_object* v___f_458_; 
v_toApplicative_452_ = lean_ctor_get(v_inst_451_, 0);
lean_inc_ref(v_toApplicative_452_);
v_toBind_453_ = lean_ctor_get(v_inst_451_, 1);
lean_inc(v_toBind_453_);
lean_dec_ref(v_inst_451_);
v_toPure_454_ = lean_ctor_get(v_toApplicative_452_, 1);
lean_inc(v_toPure_454_);
lean_dec_ref(v_toApplicative_452_);
lean_inc(v_toBind_453_);
v___f_455_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_455_, 0, v_inst_450_);
lean_closure_set(v___f_455_, 1, v_toBind_453_);
v___f_456_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_456_, 0, v_toPure_454_);
v___f_457_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_457_, 0, v_toBind_453_);
lean_closure_set(v___f_457_, 1, v___f_456_);
lean_closure_set(v___f_457_, 2, v_inst_449_);
lean_closure_set(v___f_457_, 3, v___f_455_);
v___f_458_ = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(v___f_458_, 0, v___f_457_);
return v___f_458_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop(lean_object* v_m_459_, lean_object* v_n_460_, lean_object* v_00_u03b1_461_, lean_object* v_00_u03b2_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_inst_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Std_IterM_Partial_instForInOfIteratorLoop___redArg(v_inst_464_, v_inst_465_, v_inst_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop___boxed(lean_object* v_m_468_, lean_object* v_n_469_, lean_object* v_00_u03b1_470_, lean_object* v_00_u03b2_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_inst_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Std_IterM_Partial_instForInOfIteratorLoop(v_m_468_, v_n_469_, v_00_u03b1_470_, v_00_u03b2_471_, v_inst_472_, v_inst_473_, v_inst_474_, v_inst_475_);
lean_dec(v_inst_472_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___redArg(lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_inst_479_){
_start:
{
lean_object* v_toApplicative_480_; lean_object* v_toBind_481_; lean_object* v_toPure_482_; lean_object* v___f_483_; lean_object* v___f_484_; lean_object* v___f_485_; lean_object* v___f_486_; 
v_toApplicative_480_ = lean_ctor_get(v_inst_479_, 0);
lean_inc_ref(v_toApplicative_480_);
v_toBind_481_ = lean_ctor_get(v_inst_479_, 1);
lean_inc(v_toBind_481_);
lean_dec_ref(v_inst_479_);
v_toPure_482_ = lean_ctor_get(v_toApplicative_480_, 1);
lean_inc(v_toPure_482_);
lean_dec_ref(v_toApplicative_480_);
lean_inc(v_toBind_481_);
v___f_483_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_483_, 0, v_inst_478_);
lean_closure_set(v___f_483_, 1, v_toBind_481_);
v___f_484_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_484_, 0, v_toPure_482_);
v___f_485_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_485_, 0, v_toBind_481_);
lean_closure_set(v___f_485_, 1, v___f_484_);
lean_closure_set(v___f_485_, 2, v_inst_477_);
lean_closure_set(v___f_485_, 3, v___f_483_);
v___f_486_ = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(v___f_486_, 0, v___f_485_);
return v___f_486_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite(lean_object* v_m_487_, lean_object* v_n_488_, lean_object* v_00_u03b1_489_, lean_object* v_00_u03b2_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_inst_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___redArg(v_inst_492_, v_inst_493_, v_inst_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___boxed(lean_object* v_m_497_, lean_object* v_n_498_, lean_object* v_00_u03b1_499_, lean_object* v_00_u03b2_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_inst_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite(v_m_497_, v_n_498_, v_00_u03b1_499_, v_00_u03b2_500_, v_inst_501_, v_inst_502_, v_inst_503_, v_inst_504_, v_inst_505_);
lean_dec(v_inst_501_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1(lean_object* v_toPure_507_, lean_object* v_____do__lift_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = lean_apply_2(v_toPure_507_, lean_box(0), v_____do__lift_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__0(lean_object* v___x_510_, lean_object* v_toPure_511_, lean_object* v_____r_512_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_510_);
v___x_514_ = lean_apply_2(v_toPure_511_, lean_box(0), v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__2(lean_object* v_f_515_, lean_object* v_toBind_516_, lean_object* v___f_517_, lean_object* v___f_518_, lean_object* v_x1_519_, lean_object* v_x2_520_, lean_object* v_x3_521_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_522_ = lean_apply_1(v_f_515_, v_x1_519_);
lean_inc(v_toBind_516_);
v___x_523_ = lean_apply_4(v_toBind_516_, lean_box(0), lean_box(0), v___x_522_, v___f_517_);
v___x_524_ = lean_apply_4(v_toBind_516_, lean_box(0), lean_box(0), v___x_523_, v___f_518_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3(lean_object* v_toPure_525_, lean_object* v_toBind_526_, lean_object* v___f_527_, lean_object* v_inst_528_, lean_object* v___f_529_, lean_object* v_it_530_, lean_object* v_f_531_){
_start:
{
lean_object* v___x_532_; lean_object* v___f_533_; lean_object* v___f_534_; lean_object* v___x_535_; 
v___x_532_ = lean_box(0);
v___f_533_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__0), 3, 2);
lean_closure_set(v___f_533_, 0, v___x_532_);
lean_closure_set(v___f_533_, 1, v_toPure_525_);
v___f_534_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__2), 7, 4);
lean_closure_set(v___f_534_, 0, v_f_531_);
lean_closure_set(v___f_534_, 1, v_toBind_526_);
lean_closure_set(v___f_534_, 2, v___f_533_);
lean_closure_set(v___f_534_, 3, v___f_527_);
v___x_535_ = lean_apply_6(v_inst_528_, v___f_529_, lean_box(0), lean_box(0), v_it_530_, v___x_532_, v___f_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg(lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_inst_538_){
_start:
{
lean_object* v_toApplicative_539_; lean_object* v_toBind_540_; lean_object* v_toPure_541_; lean_object* v___f_542_; lean_object* v___f_543_; lean_object* v___f_544_; 
v_toApplicative_539_ = lean_ctor_get(v_inst_537_, 0);
lean_inc_ref(v_toApplicative_539_);
v_toBind_540_ = lean_ctor_get(v_inst_537_, 1);
lean_inc(v_toBind_540_);
lean_dec_ref(v_inst_537_);
v_toPure_541_ = lean_ctor_get(v_toApplicative_539_, 1);
lean_inc(v_toPure_541_);
lean_dec_ref(v_toApplicative_539_);
lean_inc(v_toBind_540_);
v___f_542_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_542_, 0, v_inst_538_);
lean_closure_set(v___f_542_, 1, v_toBind_540_);
lean_inc(v_toPure_541_);
v___f_543_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_543_, 0, v_toPure_541_);
v___f_544_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3), 7, 5);
lean_closure_set(v___f_544_, 0, v_toPure_541_);
lean_closure_set(v___f_544_, 1, v_toBind_540_);
lean_closure_set(v___f_544_, 2, v___f_543_);
lean_closure_set(v___f_544_, 3, v_inst_536_);
lean_closure_set(v___f_544_, 4, v___f_542_);
return v___f_544_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop(lean_object* v_m_545_, lean_object* v_n_546_, lean_object* v_00_u03b1_547_, lean_object* v_00_u03b2_548_, lean_object* v_inst_549_, lean_object* v_inst_550_, lean_object* v_inst_551_, lean_object* v_inst_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_IterM_instForMOfIteratorLoop___redArg(v_inst_550_, v_inst_551_, v_inst_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___boxed(lean_object* v_m_554_, lean_object* v_n_555_, lean_object* v_00_u03b1_556_, lean_object* v_00_u03b2_557_, lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_inst_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_IterM_instForMOfIteratorLoop(v_m_554_, v_n_555_, v_00_u03b1_556_, v_00_u03b2_557_, v_inst_558_, v_inst_559_, v_inst_560_, v_inst_561_);
lean_dec(v_inst_558_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop___redArg(lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_inst_565_){
_start:
{
lean_object* v_toApplicative_566_; lean_object* v_toBind_567_; lean_object* v_toPure_568_; lean_object* v___f_569_; lean_object* v___f_570_; lean_object* v___f_571_; 
v_toApplicative_566_ = lean_ctor_get(v_inst_563_, 0);
lean_inc_ref(v_toApplicative_566_);
v_toBind_567_ = lean_ctor_get(v_inst_563_, 1);
lean_inc(v_toBind_567_);
lean_dec_ref(v_inst_563_);
v_toPure_568_ = lean_ctor_get(v_toApplicative_566_, 1);
lean_inc(v_toPure_568_);
lean_dec_ref(v_toApplicative_566_);
lean_inc(v_toBind_567_);
v___f_569_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_569_, 0, v_inst_565_);
lean_closure_set(v___f_569_, 1, v_toBind_567_);
lean_inc(v_toPure_568_);
v___f_570_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_570_, 0, v_toPure_568_);
v___f_571_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3), 7, 5);
lean_closure_set(v___f_571_, 0, v_toPure_568_);
lean_closure_set(v___f_571_, 1, v_toBind_567_);
lean_closure_set(v___f_571_, 2, v___f_570_);
lean_closure_set(v___f_571_, 3, v_inst_564_);
lean_closure_set(v___f_571_, 4, v___f_569_);
return v___f_571_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop(lean_object* v_m_572_, lean_object* v_n_573_, lean_object* v_00_u03b1_574_, lean_object* v_00_u03b2_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_inst_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_IterM_Partial_instForMOfItreratorLoop___redArg(v_inst_576_, v_inst_578_, v_inst_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop___boxed(lean_object* v_m_581_, lean_object* v_n_582_, lean_object* v_00_u03b1_583_, lean_object* v_00_u03b2_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Std_IterM_Partial_instForMOfItreratorLoop(v_m_581_, v_n_582_, v_00_u03b1_583_, v_00_u03b2_584_, v_inst_585_, v_inst_586_, v_inst_587_, v_inst_588_);
lean_dec(v_inst_586_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___redArg(lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_){
_start:
{
lean_object* v_toApplicative_593_; lean_object* v_toBind_594_; lean_object* v_toPure_595_; lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___f_598_; 
v_toApplicative_593_ = lean_ctor_get(v_inst_591_, 0);
lean_inc_ref(v_toApplicative_593_);
v_toBind_594_ = lean_ctor_get(v_inst_591_, 1);
lean_inc(v_toBind_594_);
lean_dec_ref(v_inst_591_);
v_toPure_595_ = lean_ctor_get(v_toApplicative_593_, 1);
lean_inc(v_toPure_595_);
lean_dec_ref(v_toApplicative_593_);
lean_inc(v_toBind_594_);
v___f_596_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_596_, 0, v_inst_592_);
lean_closure_set(v___f_596_, 1, v_toBind_594_);
lean_inc(v_toPure_595_);
v___f_597_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_597_, 0, v_toPure_595_);
v___f_598_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3), 7, 5);
lean_closure_set(v___f_598_, 0, v_toPure_595_);
lean_closure_set(v___f_598_, 1, v_toBind_594_);
lean_closure_set(v___f_598_, 2, v___f_597_);
lean_closure_set(v___f_598_, 3, v_inst_590_);
lean_closure_set(v___f_598_, 4, v___f_596_);
return v___f_598_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite(lean_object* v_m_599_, lean_object* v_n_600_, lean_object* v_00_u03b1_601_, lean_object* v_00_u03b2_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_inst_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___redArg(v_inst_604_, v_inst_605_, v_inst_606_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___boxed(lean_object* v_m_609_, lean_object* v_n_610_, lean_object* v_00_u03b1_611_, lean_object* v_00_u03b2_612_, lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_inst_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite(v_m_609_, v_n_610_, v_00_u03b1_611_, v_00_u03b2_612_, v_inst_613_, v_inst_614_, v_inst_615_, v_inst_616_, v_inst_617_);
lean_dec(v_inst_613_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg___lam__0(lean_object* v_a_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_620_, 0, v_a_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg___lam__3(lean_object* v_toFunctor_621_, lean_object* v_f_622_, lean_object* v___f_623_, lean_object* v_toBind_624_, lean_object* v___f_625_, lean_object* v_x1_626_, lean_object* v_x2_627_, lean_object* v_x3_628_){
_start:
{
lean_object* v_map_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_map_629_ = lean_ctor_get(v_toFunctor_621_, 0);
lean_inc(v_map_629_);
lean_dec_ref(v_toFunctor_621_);
v___x_630_ = lean_apply_2(v_f_622_, v_x3_628_, v_x1_626_);
v___x_631_ = lean_apply_4(v_map_629_, lean_box(0), lean_box(0), v___f_623_, v___x_630_);
v___x_632_ = lean_apply_4(v_toBind_624_, lean_box(0), lean_box(0), v___x_631_, v___f_625_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg(lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_inst_636_, lean_object* v_f_637_, lean_object* v_init_638_, lean_object* v_it_639_){
_start:
{
lean_object* v_toApplicative_640_; lean_object* v_toBind_641_; lean_object* v_toFunctor_642_; lean_object* v_toPure_643_; lean_object* v___f_644_; lean_object* v___f_645_; lean_object* v___f_646_; lean_object* v___f_647_; lean_object* v___x_648_; 
v_toApplicative_640_ = lean_ctor_get(v_inst_634_, 0);
lean_inc_ref(v_toApplicative_640_);
v_toBind_641_ = lean_ctor_get(v_inst_634_, 1);
lean_inc(v_toBind_641_);
lean_dec_ref(v_inst_634_);
v_toFunctor_642_ = lean_ctor_get(v_toApplicative_640_, 0);
lean_inc_ref(v_toFunctor_642_);
v_toPure_643_ = lean_ctor_get(v_toApplicative_640_, 1);
lean_inc(v_toPure_643_);
lean_dec_ref(v_toApplicative_640_);
v___f_644_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
lean_inc(v_toBind_641_);
v___f_645_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_645_, 0, v_inst_636_);
lean_closure_set(v___f_645_, 1, v_toBind_641_);
v___f_646_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_646_, 0, v_toPure_643_);
v___f_647_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_647_, 0, v_toFunctor_642_);
lean_closure_set(v___f_647_, 1, v_f_637_);
lean_closure_set(v___f_647_, 2, v___f_644_);
lean_closure_set(v___f_647_, 3, v_toBind_641_);
lean_closure_set(v___f_647_, 4, v___f_646_);
v___x_648_ = lean_apply_6(v_inst_635_, v___f_645_, lean_box(0), lean_box(0), v_it_639_, v_init_638_, v___f_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM(lean_object* v_m_649_, lean_object* v_n_650_, lean_object* v_inst_651_, lean_object* v_00_u03b1_652_, lean_object* v_00_u03b2_653_, lean_object* v_00_u03b3_654_, lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_f_658_, lean_object* v_init_659_, lean_object* v_it_660_){
_start:
{
lean_object* v_toApplicative_661_; lean_object* v_toBind_662_; lean_object* v_toFunctor_663_; lean_object* v_toPure_664_; lean_object* v___f_665_; lean_object* v___f_666_; lean_object* v___f_667_; lean_object* v___f_668_; lean_object* v___x_669_; 
v_toApplicative_661_ = lean_ctor_get(v_inst_651_, 0);
lean_inc_ref(v_toApplicative_661_);
v_toBind_662_ = lean_ctor_get(v_inst_651_, 1);
lean_inc(v_toBind_662_);
lean_dec_ref(v_inst_651_);
v_toFunctor_663_ = lean_ctor_get(v_toApplicative_661_, 0);
lean_inc_ref(v_toFunctor_663_);
v_toPure_664_ = lean_ctor_get(v_toApplicative_661_, 1);
lean_inc(v_toPure_664_);
lean_dec_ref(v_toApplicative_661_);
v___f_665_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
lean_inc(v_toBind_662_);
v___f_666_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_666_, 0, v_inst_657_);
lean_closure_set(v___f_666_, 1, v_toBind_662_);
v___f_667_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_667_, 0, v_toPure_664_);
v___f_668_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_668_, 0, v_toFunctor_663_);
lean_closure_set(v___f_668_, 1, v_f_658_);
lean_closure_set(v___f_668_, 2, v___f_665_);
lean_closure_set(v___f_668_, 3, v_toBind_662_);
lean_closure_set(v___f_668_, 4, v___f_667_);
v___x_669_ = lean_apply_6(v_inst_656_, v___f_666_, lean_box(0), lean_box(0), v_it_660_, v_init_659_, v___f_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___boxed(lean_object* v_m_670_, lean_object* v_n_671_, lean_object* v_inst_672_, lean_object* v_00_u03b1_673_, lean_object* v_00_u03b2_674_, lean_object* v_00_u03b3_675_, lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_f_679_, lean_object* v_init_680_, lean_object* v_it_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Std_IterM_foldM(v_m_670_, v_n_671_, v_inst_672_, v_00_u03b1_673_, v_00_u03b2_674_, v_00_u03b3_675_, v_inst_676_, v_inst_677_, v_inst_678_, v_f_679_, v_init_680_, v_it_681_);
lean_dec(v_inst_676_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM___redArg(lean_object* v_inst_683_, lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_f_686_, lean_object* v_init_687_, lean_object* v_it_688_){
_start:
{
lean_object* v_toApplicative_689_; lean_object* v_toBind_690_; lean_object* v_toFunctor_691_; lean_object* v_toPure_692_; lean_object* v___f_693_; lean_object* v___f_694_; lean_object* v___f_695_; lean_object* v___f_696_; lean_object* v___x_697_; 
v_toApplicative_689_ = lean_ctor_get(v_inst_683_, 0);
lean_inc_ref(v_toApplicative_689_);
v_toBind_690_ = lean_ctor_get(v_inst_683_, 1);
lean_inc(v_toBind_690_);
lean_dec_ref(v_inst_683_);
v_toFunctor_691_ = lean_ctor_get(v_toApplicative_689_, 0);
lean_inc_ref(v_toFunctor_691_);
v_toPure_692_ = lean_ctor_get(v_toApplicative_689_, 1);
lean_inc(v_toPure_692_);
lean_dec_ref(v_toApplicative_689_);
v___f_693_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
lean_inc(v_toBind_690_);
v___f_694_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_694_, 0, v_inst_685_);
lean_closure_set(v___f_694_, 1, v_toBind_690_);
v___f_695_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_695_, 0, v_toPure_692_);
v___f_696_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_696_, 0, v_toFunctor_691_);
lean_closure_set(v___f_696_, 1, v_f_686_);
lean_closure_set(v___f_696_, 2, v___f_693_);
lean_closure_set(v___f_696_, 3, v_toBind_690_);
lean_closure_set(v___f_696_, 4, v___f_695_);
v___x_697_ = lean_apply_6(v_inst_684_, v___f_694_, lean_box(0), lean_box(0), v_it_688_, v_init_687_, v___f_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM(lean_object* v_m_698_, lean_object* v_n_699_, lean_object* v_inst_700_, lean_object* v_00_u03b1_701_, lean_object* v_00_u03b2_702_, lean_object* v_00_u03b3_703_, lean_object* v_inst_704_, lean_object* v_inst_705_, lean_object* v_inst_706_, lean_object* v_f_707_, lean_object* v_init_708_, lean_object* v_it_709_){
_start:
{
lean_object* v_toApplicative_710_; lean_object* v_toBind_711_; lean_object* v_toFunctor_712_; lean_object* v_toPure_713_; lean_object* v___f_714_; lean_object* v___f_715_; lean_object* v___f_716_; lean_object* v___f_717_; lean_object* v___x_718_; 
v_toApplicative_710_ = lean_ctor_get(v_inst_700_, 0);
lean_inc_ref(v_toApplicative_710_);
v_toBind_711_ = lean_ctor_get(v_inst_700_, 1);
lean_inc(v_toBind_711_);
lean_dec_ref(v_inst_700_);
v_toFunctor_712_ = lean_ctor_get(v_toApplicative_710_, 0);
lean_inc_ref(v_toFunctor_712_);
v_toPure_713_ = lean_ctor_get(v_toApplicative_710_, 1);
lean_inc(v_toPure_713_);
lean_dec_ref(v_toApplicative_710_);
v___f_714_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
lean_inc(v_toBind_711_);
v___f_715_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_715_, 0, v_inst_706_);
lean_closure_set(v___f_715_, 1, v_toBind_711_);
v___f_716_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_716_, 0, v_toPure_713_);
v___f_717_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_717_, 0, v_toFunctor_712_);
lean_closure_set(v___f_717_, 1, v_f_707_);
lean_closure_set(v___f_717_, 2, v___f_714_);
lean_closure_set(v___f_717_, 3, v_toBind_711_);
lean_closure_set(v___f_717_, 4, v___f_716_);
v___x_718_ = lean_apply_6(v_inst_705_, v___f_715_, lean_box(0), lean_box(0), v_it_709_, v_init_708_, v___f_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM___boxed(lean_object* v_m_719_, lean_object* v_n_720_, lean_object* v_inst_721_, lean_object* v_00_u03b1_722_, lean_object* v_00_u03b2_723_, lean_object* v_00_u03b3_724_, lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_f_728_, lean_object* v_init_729_, lean_object* v_it_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Std_IterM_Partial_foldM(v_m_719_, v_n_720_, v_inst_721_, v_00_u03b1_722_, v_00_u03b2_723_, v_00_u03b3_724_, v_inst_725_, v_inst_726_, v_inst_727_, v_f_728_, v_init_729_, v_it_730_);
lean_dec(v_inst_725_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM___redArg(lean_object* v_inst_732_, lean_object* v_inst_733_, lean_object* v_inst_734_, lean_object* v_f_735_, lean_object* v_init_736_, lean_object* v_it_737_){
_start:
{
lean_object* v_toApplicative_738_; lean_object* v_toBind_739_; lean_object* v_toFunctor_740_; lean_object* v_toPure_741_; lean_object* v___f_742_; lean_object* v___f_743_; lean_object* v___f_744_; lean_object* v___f_745_; lean_object* v___x_746_; 
v_toApplicative_738_ = lean_ctor_get(v_inst_732_, 0);
lean_inc_ref(v_toApplicative_738_);
v_toBind_739_ = lean_ctor_get(v_inst_732_, 1);
lean_inc(v_toBind_739_);
lean_dec_ref(v_inst_732_);
v_toFunctor_740_ = lean_ctor_get(v_toApplicative_738_, 0);
lean_inc_ref(v_toFunctor_740_);
v_toPure_741_ = lean_ctor_get(v_toApplicative_738_, 1);
lean_inc(v_toPure_741_);
lean_dec_ref(v_toApplicative_738_);
v___f_742_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
lean_inc(v_toBind_739_);
v___f_743_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_743_, 0, v_inst_734_);
lean_closure_set(v___f_743_, 1, v_toBind_739_);
v___f_744_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_744_, 0, v_toPure_741_);
v___f_745_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_745_, 0, v_toFunctor_740_);
lean_closure_set(v___f_745_, 1, v_f_735_);
lean_closure_set(v___f_745_, 2, v___f_742_);
lean_closure_set(v___f_745_, 3, v_toBind_739_);
lean_closure_set(v___f_745_, 4, v___f_744_);
v___x_746_ = lean_apply_6(v_inst_733_, v___f_743_, lean_box(0), lean_box(0), v_it_737_, v_init_736_, v___f_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM(lean_object* v_m_747_, lean_object* v_n_748_, lean_object* v_inst_749_, lean_object* v_00_u03b1_750_, lean_object* v_00_u03b2_751_, lean_object* v_00_u03b3_752_, lean_object* v_inst_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_f_757_, lean_object* v_init_758_, lean_object* v_it_759_){
_start:
{
lean_object* v_toApplicative_760_; lean_object* v_toBind_761_; lean_object* v_toFunctor_762_; lean_object* v_toPure_763_; lean_object* v___f_764_; lean_object* v___f_765_; lean_object* v___f_766_; lean_object* v___f_767_; lean_object* v___x_768_; 
v_toApplicative_760_ = lean_ctor_get(v_inst_749_, 0);
lean_inc_ref(v_toApplicative_760_);
v_toBind_761_ = lean_ctor_get(v_inst_749_, 1);
lean_inc(v_toBind_761_);
lean_dec_ref(v_inst_749_);
v_toFunctor_762_ = lean_ctor_get(v_toApplicative_760_, 0);
lean_inc_ref(v_toFunctor_762_);
v_toPure_763_ = lean_ctor_get(v_toApplicative_760_, 1);
lean_inc(v_toPure_763_);
lean_dec_ref(v_toApplicative_760_);
v___f_764_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
lean_inc(v_toBind_761_);
v___f_765_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_765_, 0, v_inst_755_);
lean_closure_set(v___f_765_, 1, v_toBind_761_);
v___f_766_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_766_, 0, v_toPure_763_);
v___f_767_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_767_, 0, v_toFunctor_762_);
lean_closure_set(v___f_767_, 1, v_f_757_);
lean_closure_set(v___f_767_, 2, v___f_764_);
lean_closure_set(v___f_767_, 3, v_toBind_761_);
lean_closure_set(v___f_767_, 4, v___f_766_);
v___x_768_ = lean_apply_6(v_inst_754_, v___f_765_, lean_box(0), lean_box(0), v_it_759_, v_init_758_, v___f_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM___boxed(lean_object* v_m_769_, lean_object* v_n_770_, lean_object* v_inst_771_, lean_object* v_00_u03b1_772_, lean_object* v_00_u03b2_773_, lean_object* v_00_u03b3_774_, lean_object* v_inst_775_, lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_f_779_, lean_object* v_init_780_, lean_object* v_it_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Std_IterM_Total_foldM(v_m_769_, v_n_770_, v_inst_771_, v_00_u03b1_772_, v_00_u03b2_773_, v_00_u03b3_774_, v_inst_775_, v_inst_776_, v_inst_777_, v_inst_778_, v_f_779_, v_init_780_, v_it_781_);
lean_dec(v_inst_775_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg___lam__0(lean_object* v_toBind_783_, lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v_f_786_, lean_object* v_x_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = lean_apply_4(v_toBind_783_, lean_box(0), lean_box(0), v_x_787_, v_f_786_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg___lam__2(lean_object* v_f_789_, lean_object* v_toPure_790_, lean_object* v_toBind_791_, lean_object* v___f_792_, lean_object* v_x1_793_, lean_object* v_x2_794_, lean_object* v_x3_795_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_796_ = lean_apply_2(v_f_789_, v_x3_795_, v_x1_793_);
v___x_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
v___x_798_ = lean_apply_2(v_toPure_790_, lean_box(0), v___x_797_);
v___x_799_ = lean_apply_4(v_toBind_791_, lean_box(0), lean_box(0), v___x_798_, v___f_792_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg(lean_object* v_inst_800_, lean_object* v_inst_801_, lean_object* v_f_802_, lean_object* v_init_803_, lean_object* v_it_804_){
_start:
{
lean_object* v_toApplicative_805_; lean_object* v_toBind_806_; lean_object* v_toPure_807_; lean_object* v___f_808_; lean_object* v___f_809_; lean_object* v___f_810_; lean_object* v___x_811_; 
v_toApplicative_805_ = lean_ctor_get(v_inst_800_, 0);
lean_inc_ref(v_toApplicative_805_);
v_toBind_806_ = lean_ctor_get(v_inst_800_, 1);
lean_inc(v_toBind_806_);
lean_dec_ref(v_inst_800_);
v_toPure_807_ = lean_ctor_get(v_toApplicative_805_, 1);
lean_inc(v_toPure_807_);
lean_dec_ref(v_toApplicative_805_);
lean_inc(v_toBind_806_);
v___f_808_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_808_, 0, v_toBind_806_);
lean_inc(v_toPure_807_);
v___f_809_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_809_, 0, v_toPure_807_);
v___f_810_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_810_, 0, v_f_802_);
lean_closure_set(v___f_810_, 1, v_toPure_807_);
lean_closure_set(v___f_810_, 2, v_toBind_806_);
lean_closure_set(v___f_810_, 3, v___f_809_);
v___x_811_ = lean_apply_6(v_inst_801_, v___f_808_, lean_box(0), lean_box(0), v_it_804_, v_init_803_, v___f_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold(lean_object* v_m_812_, lean_object* v_00_u03b1_813_, lean_object* v_00_u03b2_814_, lean_object* v_00_u03b3_815_, lean_object* v_inst_816_, lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_f_819_, lean_object* v_init_820_, lean_object* v_it_821_){
_start:
{
lean_object* v_toApplicative_822_; lean_object* v_toBind_823_; lean_object* v_toPure_824_; lean_object* v___f_825_; lean_object* v___f_826_; lean_object* v___f_827_; lean_object* v___x_828_; 
v_toApplicative_822_ = lean_ctor_get(v_inst_816_, 0);
lean_inc_ref(v_toApplicative_822_);
v_toBind_823_ = lean_ctor_get(v_inst_816_, 1);
lean_inc(v_toBind_823_);
lean_dec_ref(v_inst_816_);
v_toPure_824_ = lean_ctor_get(v_toApplicative_822_, 1);
lean_inc(v_toPure_824_);
lean_dec_ref(v_toApplicative_822_);
lean_inc(v_toBind_823_);
v___f_825_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_825_, 0, v_toBind_823_);
lean_inc(v_toPure_824_);
v___f_826_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_826_, 0, v_toPure_824_);
v___f_827_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_827_, 0, v_f_819_);
lean_closure_set(v___f_827_, 1, v_toPure_824_);
lean_closure_set(v___f_827_, 2, v_toBind_823_);
lean_closure_set(v___f_827_, 3, v___f_826_);
v___x_828_ = lean_apply_6(v_inst_818_, v___f_825_, lean_box(0), lean_box(0), v_it_821_, v_init_820_, v___f_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___boxed(lean_object* v_m_829_, lean_object* v_00_u03b1_830_, lean_object* v_00_u03b2_831_, lean_object* v_00_u03b3_832_, lean_object* v_inst_833_, lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_f_836_, lean_object* v_init_837_, lean_object* v_it_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_IterM_fold(v_m_829_, v_00_u03b1_830_, v_00_u03b2_831_, v_00_u03b3_832_, v_inst_833_, v_inst_834_, v_inst_835_, v_f_836_, v_init_837_, v_it_838_);
lean_dec(v_inst_834_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold___redArg(lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_f_842_, lean_object* v_init_843_, lean_object* v_it_844_){
_start:
{
lean_object* v_toApplicative_845_; lean_object* v_toBind_846_; lean_object* v_toPure_847_; lean_object* v___f_848_; lean_object* v___f_849_; lean_object* v___f_850_; lean_object* v___x_851_; 
v_toApplicative_845_ = lean_ctor_get(v_inst_840_, 0);
lean_inc_ref(v_toApplicative_845_);
v_toBind_846_ = lean_ctor_get(v_inst_840_, 1);
lean_inc(v_toBind_846_);
lean_dec_ref(v_inst_840_);
v_toPure_847_ = lean_ctor_get(v_toApplicative_845_, 1);
lean_inc(v_toPure_847_);
lean_dec_ref(v_toApplicative_845_);
lean_inc(v_toBind_846_);
v___f_848_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_848_, 0, v_toBind_846_);
lean_inc(v_toPure_847_);
v___f_849_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_849_, 0, v_toPure_847_);
v___f_850_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_850_, 0, v_f_842_);
lean_closure_set(v___f_850_, 1, v_toPure_847_);
lean_closure_set(v___f_850_, 2, v_toBind_846_);
lean_closure_set(v___f_850_, 3, v___f_849_);
v___x_851_ = lean_apply_6(v_inst_841_, v___f_848_, lean_box(0), lean_box(0), v_it_844_, v_init_843_, v___f_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold(lean_object* v_m_852_, lean_object* v_00_u03b1_853_, lean_object* v_00_u03b2_854_, lean_object* v_00_u03b3_855_, lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_f_859_, lean_object* v_init_860_, lean_object* v_it_861_){
_start:
{
lean_object* v_toApplicative_862_; lean_object* v_toBind_863_; lean_object* v_toPure_864_; lean_object* v___f_865_; lean_object* v___f_866_; lean_object* v___f_867_; lean_object* v___x_868_; 
v_toApplicative_862_ = lean_ctor_get(v_inst_856_, 0);
lean_inc_ref(v_toApplicative_862_);
v_toBind_863_ = lean_ctor_get(v_inst_856_, 1);
lean_inc(v_toBind_863_);
lean_dec_ref(v_inst_856_);
v_toPure_864_ = lean_ctor_get(v_toApplicative_862_, 1);
lean_inc(v_toPure_864_);
lean_dec_ref(v_toApplicative_862_);
lean_inc(v_toBind_863_);
v___f_865_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_865_, 0, v_toBind_863_);
lean_inc(v_toPure_864_);
v___f_866_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_866_, 0, v_toPure_864_);
v___f_867_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_867_, 0, v_f_859_);
lean_closure_set(v___f_867_, 1, v_toPure_864_);
lean_closure_set(v___f_867_, 2, v_toBind_863_);
lean_closure_set(v___f_867_, 3, v___f_866_);
v___x_868_ = lean_apply_6(v_inst_858_, v___f_865_, lean_box(0), lean_box(0), v_it_861_, v_init_860_, v___f_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold___boxed(lean_object* v_m_869_, lean_object* v_00_u03b1_870_, lean_object* v_00_u03b2_871_, lean_object* v_00_u03b3_872_, lean_object* v_inst_873_, lean_object* v_inst_874_, lean_object* v_inst_875_, lean_object* v_f_876_, lean_object* v_init_877_, lean_object* v_it_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Std_IterM_Partial_fold(v_m_869_, v_00_u03b1_870_, v_00_u03b2_871_, v_00_u03b3_872_, v_inst_873_, v_inst_874_, v_inst_875_, v_f_876_, v_init_877_, v_it_878_);
lean_dec(v_inst_874_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold___redArg(lean_object* v_inst_880_, lean_object* v_inst_881_, lean_object* v_f_882_, lean_object* v_init_883_, lean_object* v_it_884_){
_start:
{
lean_object* v_toApplicative_885_; lean_object* v_toBind_886_; lean_object* v_toPure_887_; lean_object* v___f_888_; lean_object* v___f_889_; lean_object* v___f_890_; lean_object* v___x_891_; 
v_toApplicative_885_ = lean_ctor_get(v_inst_880_, 0);
lean_inc_ref(v_toApplicative_885_);
v_toBind_886_ = lean_ctor_get(v_inst_880_, 1);
lean_inc(v_toBind_886_);
lean_dec_ref(v_inst_880_);
v_toPure_887_ = lean_ctor_get(v_toApplicative_885_, 1);
lean_inc(v_toPure_887_);
lean_dec_ref(v_toApplicative_885_);
lean_inc(v_toBind_886_);
v___f_888_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_888_, 0, v_toBind_886_);
lean_inc(v_toPure_887_);
v___f_889_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_889_, 0, v_toPure_887_);
v___f_890_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_890_, 0, v_f_882_);
lean_closure_set(v___f_890_, 1, v_toPure_887_);
lean_closure_set(v___f_890_, 2, v_toBind_886_);
lean_closure_set(v___f_890_, 3, v___f_889_);
v___x_891_ = lean_apply_6(v_inst_881_, v___f_888_, lean_box(0), lean_box(0), v_it_884_, v_init_883_, v___f_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold(lean_object* v_m_892_, lean_object* v_00_u03b1_893_, lean_object* v_00_u03b2_894_, lean_object* v_00_u03b3_895_, lean_object* v_inst_896_, lean_object* v_inst_897_, lean_object* v_inst_898_, lean_object* v_inst_899_, lean_object* v_f_900_, lean_object* v_init_901_, lean_object* v_it_902_){
_start:
{
lean_object* v_toApplicative_903_; lean_object* v_toBind_904_; lean_object* v_toPure_905_; lean_object* v___f_906_; lean_object* v___f_907_; lean_object* v___f_908_; lean_object* v___x_909_; 
v_toApplicative_903_ = lean_ctor_get(v_inst_896_, 0);
lean_inc_ref(v_toApplicative_903_);
v_toBind_904_ = lean_ctor_get(v_inst_896_, 1);
lean_inc(v_toBind_904_);
lean_dec_ref(v_inst_896_);
v_toPure_905_ = lean_ctor_get(v_toApplicative_903_, 1);
lean_inc(v_toPure_905_);
lean_dec_ref(v_toApplicative_903_);
lean_inc(v_toBind_904_);
v___f_906_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_906_, 0, v_toBind_904_);
lean_inc(v_toPure_905_);
v___f_907_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_907_, 0, v_toPure_905_);
v___f_908_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_908_, 0, v_f_900_);
lean_closure_set(v___f_908_, 1, v_toPure_905_);
lean_closure_set(v___f_908_, 2, v_toBind_904_);
lean_closure_set(v___f_908_, 3, v___f_907_);
v___x_909_ = lean_apply_6(v_inst_898_, v___f_906_, lean_box(0), lean_box(0), v_it_902_, v_init_901_, v___f_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold___boxed(lean_object* v_m_910_, lean_object* v_00_u03b1_911_, lean_object* v_00_u03b2_912_, lean_object* v_00_u03b3_913_, lean_object* v_inst_914_, lean_object* v_inst_915_, lean_object* v_inst_916_, lean_object* v_inst_917_, lean_object* v_f_918_, lean_object* v_init_919_, lean_object* v_it_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Std_IterM_Total_fold(v_m_910_, v_00_u03b1_911_, v_00_u03b2_912_, v_00_u03b3_913_, v_inst_914_, v_inst_915_, v_inst_916_, v_inst_917_, v_f_918_, v_init_919_, v_it_920_);
lean_dec(v_inst_915_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg___lam__2(lean_object* v___x_922_, lean_object* v_toPure_923_, lean_object* v_toBind_924_, lean_object* v___f_925_, lean_object* v_x1_926_, lean_object* v_x2_927_, lean_object* v_x3_928_){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_922_);
v___x_930_ = lean_apply_2(v_toPure_923_, lean_box(0), v___x_929_);
v___x_931_ = lean_apply_4(v_toBind_924_, lean_box(0), lean_box(0), v___x_930_, v___f_925_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg___lam__2___boxed(lean_object* v___x_932_, lean_object* v_toPure_933_, lean_object* v_toBind_934_, lean_object* v___f_935_, lean_object* v_x1_936_, lean_object* v_x2_937_, lean_object* v_x3_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Std_IterM_drain___redArg___lam__2(v___x_932_, v_toPure_933_, v_toBind_934_, v___f_935_, v_x1_936_, v_x2_937_, v_x3_938_);
lean_dec(v_x1_936_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg(lean_object* v_inst_940_, lean_object* v_it_941_, lean_object* v_inst_942_){
_start:
{
lean_object* v_toApplicative_943_; lean_object* v_toBind_944_; lean_object* v_toPure_945_; lean_object* v___x_946_; lean_object* v___f_947_; lean_object* v___f_948_; lean_object* v___f_949_; lean_object* v___x_950_; 
v_toApplicative_943_ = lean_ctor_get(v_inst_940_, 0);
lean_inc_ref(v_toApplicative_943_);
v_toBind_944_ = lean_ctor_get(v_inst_940_, 1);
lean_inc(v_toBind_944_);
lean_dec_ref(v_inst_940_);
v_toPure_945_ = lean_ctor_get(v_toApplicative_943_, 1);
lean_inc(v_toPure_945_);
lean_dec_ref(v_toApplicative_943_);
v___x_946_ = lean_box(0);
lean_inc(v_toBind_944_);
v___f_947_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_947_, 0, v_toBind_944_);
lean_inc(v_toPure_945_);
v___f_948_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_948_, 0, v_toPure_945_);
v___f_949_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_949_, 0, v___x_946_);
lean_closure_set(v___f_949_, 1, v_toPure_945_);
lean_closure_set(v___f_949_, 2, v_toBind_944_);
lean_closure_set(v___f_949_, 3, v___f_948_);
v___x_950_ = lean_apply_6(v_inst_942_, v___f_947_, lean_box(0), lean_box(0), v_it_941_, v___x_946_, v___f_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain(lean_object* v_00_u03b1_951_, lean_object* v_m_952_, lean_object* v_inst_953_, lean_object* v_00_u03b2_954_, lean_object* v_inst_955_, lean_object* v_it_956_, lean_object* v_inst_957_){
_start:
{
lean_object* v_toApplicative_958_; lean_object* v_toBind_959_; lean_object* v_toPure_960_; lean_object* v___x_961_; lean_object* v___f_962_; lean_object* v___f_963_; lean_object* v___f_964_; lean_object* v___x_965_; 
v_toApplicative_958_ = lean_ctor_get(v_inst_953_, 0);
lean_inc_ref(v_toApplicative_958_);
v_toBind_959_ = lean_ctor_get(v_inst_953_, 1);
lean_inc(v_toBind_959_);
lean_dec_ref(v_inst_953_);
v_toPure_960_ = lean_ctor_get(v_toApplicative_958_, 1);
lean_inc(v_toPure_960_);
lean_dec_ref(v_toApplicative_958_);
v___x_961_ = lean_box(0);
lean_inc(v_toBind_959_);
v___f_962_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_962_, 0, v_toBind_959_);
lean_inc(v_toPure_960_);
v___f_963_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_963_, 0, v_toPure_960_);
v___f_964_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_964_, 0, v___x_961_);
lean_closure_set(v___f_964_, 1, v_toPure_960_);
lean_closure_set(v___f_964_, 2, v_toBind_959_);
lean_closure_set(v___f_964_, 3, v___f_963_);
v___x_965_ = lean_apply_6(v_inst_957_, v___f_962_, lean_box(0), lean_box(0), v_it_956_, v___x_961_, v___f_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___boxed(lean_object* v_00_u03b1_966_, lean_object* v_m_967_, lean_object* v_inst_968_, lean_object* v_00_u03b2_969_, lean_object* v_inst_970_, lean_object* v_it_971_, lean_object* v_inst_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Std_IterM_drain(v_00_u03b1_966_, v_m_967_, v_inst_968_, v_00_u03b2_969_, v_inst_970_, v_it_971_, v_inst_972_);
lean_dec(v_inst_970_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain___redArg(lean_object* v_inst_974_, lean_object* v_it_975_, lean_object* v_inst_976_){
_start:
{
lean_object* v_toApplicative_977_; lean_object* v_toBind_978_; lean_object* v_toPure_979_; lean_object* v___x_980_; lean_object* v___f_981_; lean_object* v___f_982_; lean_object* v___f_983_; lean_object* v___x_984_; 
v_toApplicative_977_ = lean_ctor_get(v_inst_974_, 0);
lean_inc_ref(v_toApplicative_977_);
v_toBind_978_ = lean_ctor_get(v_inst_974_, 1);
lean_inc(v_toBind_978_);
lean_dec_ref(v_inst_974_);
v_toPure_979_ = lean_ctor_get(v_toApplicative_977_, 1);
lean_inc(v_toPure_979_);
lean_dec_ref(v_toApplicative_977_);
v___x_980_ = lean_box(0);
lean_inc(v_toBind_978_);
v___f_981_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_981_, 0, v_toBind_978_);
lean_inc(v_toPure_979_);
v___f_982_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_982_, 0, v_toPure_979_);
v___f_983_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_983_, 0, v___x_980_);
lean_closure_set(v___f_983_, 1, v_toPure_979_);
lean_closure_set(v___f_983_, 2, v_toBind_978_);
lean_closure_set(v___f_983_, 3, v___f_982_);
v___x_984_ = lean_apply_6(v_inst_976_, v___f_981_, lean_box(0), lean_box(0), v_it_975_, v___x_980_, v___f_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain(lean_object* v_00_u03b1_985_, lean_object* v_m_986_, lean_object* v_inst_987_, lean_object* v_00_u03b2_988_, lean_object* v_inst_989_, lean_object* v_it_990_, lean_object* v_inst_991_){
_start:
{
lean_object* v_toApplicative_992_; lean_object* v_toBind_993_; lean_object* v_toPure_994_; lean_object* v___x_995_; lean_object* v___f_996_; lean_object* v___f_997_; lean_object* v___f_998_; lean_object* v___x_999_; 
v_toApplicative_992_ = lean_ctor_get(v_inst_987_, 0);
lean_inc_ref(v_toApplicative_992_);
v_toBind_993_ = lean_ctor_get(v_inst_987_, 1);
lean_inc(v_toBind_993_);
lean_dec_ref(v_inst_987_);
v_toPure_994_ = lean_ctor_get(v_toApplicative_992_, 1);
lean_inc(v_toPure_994_);
lean_dec_ref(v_toApplicative_992_);
v___x_995_ = lean_box(0);
lean_inc(v_toBind_993_);
v___f_996_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_996_, 0, v_toBind_993_);
lean_inc(v_toPure_994_);
v___f_997_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_997_, 0, v_toPure_994_);
v___f_998_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_998_, 0, v___x_995_);
lean_closure_set(v___f_998_, 1, v_toPure_994_);
lean_closure_set(v___f_998_, 2, v_toBind_993_);
lean_closure_set(v___f_998_, 3, v___f_997_);
v___x_999_ = lean_apply_6(v_inst_991_, v___f_996_, lean_box(0), lean_box(0), v_it_990_, v___x_995_, v___f_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain___boxed(lean_object* v_00_u03b1_1000_, lean_object* v_m_1001_, lean_object* v_inst_1002_, lean_object* v_00_u03b2_1003_, lean_object* v_inst_1004_, lean_object* v_it_1005_, lean_object* v_inst_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Std_IterM_Partial_drain(v_00_u03b1_1000_, v_m_1001_, v_inst_1002_, v_00_u03b2_1003_, v_inst_1004_, v_it_1005_, v_inst_1006_);
lean_dec(v_inst_1004_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain___redArg(lean_object* v_inst_1008_, lean_object* v_it_1009_, lean_object* v_inst_1010_){
_start:
{
lean_object* v_toApplicative_1011_; lean_object* v_toBind_1012_; lean_object* v_toPure_1013_; lean_object* v___x_1014_; lean_object* v___f_1015_; lean_object* v___f_1016_; lean_object* v___f_1017_; lean_object* v___x_1018_; 
v_toApplicative_1011_ = lean_ctor_get(v_inst_1008_, 0);
lean_inc_ref(v_toApplicative_1011_);
v_toBind_1012_ = lean_ctor_get(v_inst_1008_, 1);
lean_inc(v_toBind_1012_);
lean_dec_ref(v_inst_1008_);
v_toPure_1013_ = lean_ctor_get(v_toApplicative_1011_, 1);
lean_inc(v_toPure_1013_);
lean_dec_ref(v_toApplicative_1011_);
v___x_1014_ = lean_box(0);
lean_inc(v_toBind_1012_);
v___f_1015_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1015_, 0, v_toBind_1012_);
lean_inc(v_toPure_1013_);
v___f_1016_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1016_, 0, v_toPure_1013_);
v___f_1017_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1017_, 0, v___x_1014_);
lean_closure_set(v___f_1017_, 1, v_toPure_1013_);
lean_closure_set(v___f_1017_, 2, v_toBind_1012_);
lean_closure_set(v___f_1017_, 3, v___f_1016_);
v___x_1018_ = lean_apply_6(v_inst_1010_, v___f_1015_, lean_box(0), lean_box(0), v_it_1009_, v___x_1014_, v___f_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain(lean_object* v_00_u03b1_1019_, lean_object* v_m_1020_, lean_object* v_inst_1021_, lean_object* v_00_u03b2_1022_, lean_object* v_inst_1023_, lean_object* v_inst_1024_, lean_object* v_it_1025_, lean_object* v_inst_1026_){
_start:
{
lean_object* v_toApplicative_1027_; lean_object* v_toBind_1028_; lean_object* v_toPure_1029_; lean_object* v___x_1030_; lean_object* v___f_1031_; lean_object* v___f_1032_; lean_object* v___f_1033_; lean_object* v___x_1034_; 
v_toApplicative_1027_ = lean_ctor_get(v_inst_1021_, 0);
lean_inc_ref(v_toApplicative_1027_);
v_toBind_1028_ = lean_ctor_get(v_inst_1021_, 1);
lean_inc(v_toBind_1028_);
lean_dec_ref(v_inst_1021_);
v_toPure_1029_ = lean_ctor_get(v_toApplicative_1027_, 1);
lean_inc(v_toPure_1029_);
lean_dec_ref(v_toApplicative_1027_);
v___x_1030_ = lean_box(0);
lean_inc(v_toBind_1028_);
v___f_1031_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1031_, 0, v_toBind_1028_);
lean_inc(v_toPure_1029_);
v___f_1032_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1032_, 0, v_toPure_1029_);
v___f_1033_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1033_, 0, v___x_1030_);
lean_closure_set(v___f_1033_, 1, v_toPure_1029_);
lean_closure_set(v___f_1033_, 2, v_toBind_1028_);
lean_closure_set(v___f_1033_, 3, v___f_1032_);
v___x_1034_ = lean_apply_6(v_inst_1026_, v___f_1031_, lean_box(0), lean_box(0), v_it_1025_, v___x_1030_, v___f_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain___boxed(lean_object* v_00_u03b1_1035_, lean_object* v_m_1036_, lean_object* v_inst_1037_, lean_object* v_00_u03b2_1038_, lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_it_1041_, lean_object* v_inst_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Std_IterM_Total_drain(v_00_u03b1_1035_, v_m_1036_, v_inst_1037_, v_00_u03b2_1038_, v_inst_1039_, v_inst_1040_, v_it_1041_, v_inst_1042_);
lean_dec(v_inst_1039_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__1(lean_object* v_toPure_1044_, lean_object* v_____do__lift_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_apply_2(v_toPure_1044_, lean_box(0), v_____do__lift_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__0(uint8_t v___x_1047_, lean_object* v_toPure_1048_, uint8_t v_____do__lift_1049_){
_start:
{
if (v_____do__lift_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1050_ = lean_box(v___x_1047_);
v___x_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
v___x_1052_ = lean_apply_2(v_toPure_1048_, lean_box(0), v___x_1051_);
return v___x_1052_;
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1053_ = lean_box(v_____do__lift_1049_);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
v___x_1055_ = lean_apply_2(v_toPure_1048_, lean_box(0), v___x_1054_);
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__0___boxed(lean_object* v___x_1056_, lean_object* v_toPure_1057_, lean_object* v_____do__lift_1058_){
_start:
{
uint8_t v___x_203__boxed_1059_; uint8_t v_____do__lift_204__boxed_1060_; lean_object* v_res_1061_; 
v___x_203__boxed_1059_ = lean_unbox(v___x_1056_);
v_____do__lift_204__boxed_1060_ = lean_unbox(v_____do__lift_1058_);
v_res_1061_ = l_Std_IterM_anyM___redArg___lam__0(v___x_203__boxed_1059_, v_toPure_1057_, v_____do__lift_204__boxed_1060_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__2(lean_object* v_p_1062_, lean_object* v_toBind_1063_, lean_object* v___f_1064_, lean_object* v___f_1065_, lean_object* v_x1_1066_, lean_object* v_x2_1067_, uint8_t v_x3_1068_){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1069_ = lean_apply_1(v_p_1062_, v_x1_1066_);
lean_inc(v_toBind_1063_);
v___x_1070_ = lean_apply_4(v_toBind_1063_, lean_box(0), lean_box(0), v___x_1069_, v___f_1064_);
v___x_1071_ = lean_apply_4(v_toBind_1063_, lean_box(0), lean_box(0), v___x_1070_, v___f_1065_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__2___boxed(lean_object* v_p_1072_, lean_object* v_toBind_1073_, lean_object* v___f_1074_, lean_object* v___f_1075_, lean_object* v_x1_1076_, lean_object* v_x2_1077_, lean_object* v_x3_1078_){
_start:
{
uint8_t v_x3_225__boxed_1079_; lean_object* v_res_1080_; 
v_x3_225__boxed_1079_ = lean_unbox(v_x3_1078_);
v_res_1080_ = l_Std_IterM_anyM___redArg___lam__2(v_p_1072_, v_toBind_1073_, v___f_1074_, v___f_1075_, v_x1_1076_, v_x2_1077_, v_x3_225__boxed_1079_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg(lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_p_1083_, lean_object* v_it_1084_){
_start:
{
lean_object* v_toApplicative_1085_; lean_object* v_toBind_1086_; lean_object* v_toPure_1087_; lean_object* v___f_1088_; lean_object* v___f_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___f_1092_; lean_object* v___f_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_toApplicative_1085_ = lean_ctor_get(v_inst_1081_, 0);
lean_inc_ref(v_toApplicative_1085_);
v_toBind_1086_ = lean_ctor_get(v_inst_1081_, 1);
lean_inc(v_toBind_1086_);
lean_dec_ref(v_inst_1081_);
v_toPure_1087_ = lean_ctor_get(v_toApplicative_1085_, 1);
lean_inc(v_toPure_1087_);
lean_dec_ref(v_toApplicative_1085_);
lean_inc(v_toBind_1086_);
v___f_1088_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1088_, 0, v_toBind_1086_);
lean_inc(v_toPure_1087_);
v___f_1089_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1089_, 0, v_toPure_1087_);
v___x_1090_ = 0;
v___x_1091_ = lean_box(v___x_1090_);
v___f_1092_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1092_, 0, v___x_1091_);
lean_closure_set(v___f_1092_, 1, v_toPure_1087_);
v___f_1093_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1093_, 0, v_p_1083_);
lean_closure_set(v___f_1093_, 1, v_toBind_1086_);
lean_closure_set(v___f_1093_, 2, v___f_1092_);
lean_closure_set(v___f_1093_, 3, v___f_1089_);
v___x_1094_ = lean_box(v___x_1090_);
v___x_1095_ = lean_apply_6(v_inst_1082_, v___f_1088_, lean_box(0), lean_box(0), v_it_1084_, v___x_1094_, v___f_1093_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM(lean_object* v_00_u03b1_1096_, lean_object* v_00_u03b2_1097_, lean_object* v_m_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_p_1102_, lean_object* v_it_1103_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Std_IterM_anyM___redArg(v_inst_1099_, v_inst_1101_, v_p_1102_, v_it_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___boxed(lean_object* v_00_u03b1_1105_, lean_object* v_00_u03b2_1106_, lean_object* v_m_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_inst_1110_, lean_object* v_p_1111_, lean_object* v_it_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Std_IterM_anyM(v_00_u03b1_1105_, v_00_u03b2_1106_, v_m_1107_, v_inst_1108_, v_inst_1109_, v_inst_1110_, v_p_1111_, v_it_1112_);
lean_dec(v_inst_1109_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM___redArg(lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_p_1116_, lean_object* v_it_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Std_IterM_anyM___redArg(v_inst_1114_, v_inst_1115_, v_p_1116_, v_it_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM(lean_object* v_00_u03b1_1119_, lean_object* v_00_u03b2_1120_, lean_object* v_m_1121_, lean_object* v_inst_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_p_1125_, lean_object* v_it_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Std_IterM_anyM___redArg(v_inst_1122_, v_inst_1124_, v_p_1125_, v_it_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM___boxed(lean_object* v_00_u03b1_1128_, lean_object* v_00_u03b2_1129_, lean_object* v_m_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_inst_1133_, lean_object* v_p_1134_, lean_object* v_it_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Std_IterM_Partial_anyM(v_00_u03b1_1128_, v_00_u03b2_1129_, v_m_1130_, v_inst_1131_, v_inst_1132_, v_inst_1133_, v_p_1134_, v_it_1135_);
lean_dec(v_inst_1132_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM___redArg(lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_p_1139_, lean_object* v_it_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Std_IterM_anyM___redArg(v_inst_1137_, v_inst_1138_, v_p_1139_, v_it_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM(lean_object* v_00_u03b1_1142_, lean_object* v_00_u03b2_1143_, lean_object* v_m_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_inst_1148_, lean_object* v_p_1149_, lean_object* v_it_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Std_IterM_anyM___redArg(v_inst_1145_, v_inst_1147_, v_p_1149_, v_it_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM___boxed(lean_object* v_00_u03b1_1152_, lean_object* v_00_u03b2_1153_, lean_object* v_m_1154_, lean_object* v_inst_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_, lean_object* v_p_1159_, lean_object* v_it_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Std_IterM_Total_anyM(v_00_u03b1_1152_, v_00_u03b2_1153_, v_m_1154_, v_inst_1155_, v_inst_1156_, v_inst_1157_, v_inst_1158_, v_p_1159_, v_it_1160_);
lean_dec(v_inst_1156_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any___redArg___lam__0(lean_object* v_p_1162_, lean_object* v_toPure_1163_, lean_object* v_x_1164_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_apply_1(v_p_1162_, v_x_1164_);
v___x_1166_ = lean_apply_2(v_toPure_1163_, lean_box(0), v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any___redArg(lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_p_1169_, lean_object* v_it_1170_){
_start:
{
lean_object* v_toApplicative_1171_; lean_object* v_toPure_1172_; lean_object* v___f_1173_; lean_object* v___x_1174_; 
v_toApplicative_1171_ = lean_ctor_get(v_inst_1167_, 0);
v_toPure_1172_ = lean_ctor_get(v_toApplicative_1171_, 1);
lean_inc(v_toPure_1172_);
v___f_1173_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1173_, 0, v_p_1169_);
lean_closure_set(v___f_1173_, 1, v_toPure_1172_);
v___x_1174_ = l_Std_IterM_anyM___redArg(v_inst_1167_, v_inst_1168_, v___f_1173_, v_it_1170_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any(lean_object* v_00_u03b1_1175_, lean_object* v_00_u03b2_1176_, lean_object* v_m_1177_, lean_object* v_inst_1178_, lean_object* v_inst_1179_, lean_object* v_inst_1180_, lean_object* v_p_1181_, lean_object* v_it_1182_){
_start:
{
lean_object* v_toApplicative_1183_; lean_object* v_toPure_1184_; lean_object* v___f_1185_; lean_object* v___x_1186_; 
v_toApplicative_1183_ = lean_ctor_get(v_inst_1178_, 0);
v_toPure_1184_ = lean_ctor_get(v_toApplicative_1183_, 1);
lean_inc(v_toPure_1184_);
v___f_1185_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1185_, 0, v_p_1181_);
lean_closure_set(v___f_1185_, 1, v_toPure_1184_);
v___x_1186_ = l_Std_IterM_anyM___redArg(v_inst_1178_, v_inst_1180_, v___f_1185_, v_it_1182_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any___boxed(lean_object* v_00_u03b1_1187_, lean_object* v_00_u03b2_1188_, lean_object* v_m_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_p_1193_, lean_object* v_it_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Std_IterM_any(v_00_u03b1_1187_, v_00_u03b2_1188_, v_m_1189_, v_inst_1190_, v_inst_1191_, v_inst_1192_, v_p_1193_, v_it_1194_);
lean_dec(v_inst_1191_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any___redArg(lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_p_1198_, lean_object* v_it_1199_){
_start:
{
lean_object* v_toApplicative_1200_; lean_object* v_toPure_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; 
v_toApplicative_1200_ = lean_ctor_get(v_inst_1196_, 0);
v_toPure_1201_ = lean_ctor_get(v_toApplicative_1200_, 1);
lean_inc(v_toPure_1201_);
v___f_1202_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1202_, 0, v_p_1198_);
lean_closure_set(v___f_1202_, 1, v_toPure_1201_);
v___x_1203_ = l_Std_IterM_anyM___redArg(v_inst_1196_, v_inst_1197_, v___f_1202_, v_it_1199_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any(lean_object* v_00_u03b1_1204_, lean_object* v_00_u03b2_1205_, lean_object* v_m_1206_, lean_object* v_inst_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_p_1210_, lean_object* v_it_1211_){
_start:
{
lean_object* v_toApplicative_1212_; lean_object* v_toPure_1213_; lean_object* v___f_1214_; lean_object* v___x_1215_; 
v_toApplicative_1212_ = lean_ctor_get(v_inst_1207_, 0);
v_toPure_1213_ = lean_ctor_get(v_toApplicative_1212_, 1);
lean_inc(v_toPure_1213_);
v___f_1214_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1214_, 0, v_p_1210_);
lean_closure_set(v___f_1214_, 1, v_toPure_1213_);
v___x_1215_ = l_Std_IterM_anyM___redArg(v_inst_1207_, v_inst_1209_, v___f_1214_, v_it_1211_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any___boxed(lean_object* v_00_u03b1_1216_, lean_object* v_00_u03b2_1217_, lean_object* v_m_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_p_1222_, lean_object* v_it_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Std_IterM_Partial_any(v_00_u03b1_1216_, v_00_u03b2_1217_, v_m_1218_, v_inst_1219_, v_inst_1220_, v_inst_1221_, v_p_1222_, v_it_1223_);
lean_dec(v_inst_1220_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_any___redArg(lean_object* v_inst_1225_, lean_object* v_inst_1226_, lean_object* v_p_1227_, lean_object* v_it_1228_){
_start:
{
lean_object* v_toApplicative_1229_; lean_object* v_toPure_1230_; lean_object* v___f_1231_; lean_object* v___x_1232_; 
v_toApplicative_1229_ = lean_ctor_get(v_inst_1225_, 0);
v_toPure_1230_ = lean_ctor_get(v_toApplicative_1229_, 1);
lean_inc(v_toPure_1230_);
v___f_1231_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1231_, 0, v_p_1227_);
lean_closure_set(v___f_1231_, 1, v_toPure_1230_);
v___x_1232_ = l_Std_IterM_anyM___redArg(v_inst_1225_, v_inst_1226_, v___f_1231_, v_it_1228_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_any(lean_object* v_00_u03b1_1233_, lean_object* v_00_u03b2_1234_, lean_object* v_m_1235_, lean_object* v_inst_1236_, lean_object* v_inst_1237_, lean_object* v_inst_1238_, lean_object* v_inst_1239_, lean_object* v_p_1240_, lean_object* v_it_1241_){
_start:
{
lean_object* v_toApplicative_1242_; lean_object* v_toPure_1243_; lean_object* v___f_1244_; lean_object* v___x_1245_; 
v_toApplicative_1242_ = lean_ctor_get(v_inst_1236_, 0);
v_toPure_1243_ = lean_ctor_get(v_toApplicative_1242_, 1);
lean_inc(v_toPure_1243_);
v___f_1244_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1244_, 0, v_p_1240_);
lean_closure_set(v___f_1244_, 1, v_toPure_1243_);
v___x_1245_ = l_Std_IterM_anyM___redArg(v_inst_1236_, v_inst_1238_, v___f_1244_, v_it_1241_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_any___boxed(lean_object* v_00_u03b1_1246_, lean_object* v_00_u03b2_1247_, lean_object* v_m_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_p_1253_, lean_object* v_it_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Std_IterM_Total_any(v_00_u03b1_1246_, v_00_u03b2_1247_, v_m_1248_, v_inst_1249_, v_inst_1250_, v_inst_1251_, v_inst_1252_, v_p_1253_, v_it_1254_);
lean_dec(v_inst_1250_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg___lam__2(lean_object* v_toPure_1256_, uint8_t v___x_1257_, uint8_t v_____do__lift_1258_){
_start:
{
if (v_____do__lift_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = lean_box(v_____do__lift_1258_);
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
v___x_1261_ = lean_apply_2(v_toPure_1256_, lean_box(0), v___x_1260_);
return v___x_1261_;
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = lean_box(v___x_1257_);
v___x_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
v___x_1264_ = lean_apply_2(v_toPure_1256_, lean_box(0), v___x_1263_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg___lam__2___boxed(lean_object* v_toPure_1265_, lean_object* v___x_1266_, lean_object* v_____do__lift_1267_){
_start:
{
uint8_t v___x_201__boxed_1268_; uint8_t v_____do__lift_202__boxed_1269_; lean_object* v_res_1270_; 
v___x_201__boxed_1268_ = lean_unbox(v___x_1266_);
v_____do__lift_202__boxed_1269_ = lean_unbox(v_____do__lift_1267_);
v_res_1270_ = l_Std_IterM_allM___redArg___lam__2(v_toPure_1265_, v___x_201__boxed_1268_, v_____do__lift_202__boxed_1269_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg(lean_object* v_inst_1271_, lean_object* v_inst_1272_, lean_object* v_p_1273_, lean_object* v_it_1274_){
_start:
{
lean_object* v_toApplicative_1275_; lean_object* v_toBind_1276_; lean_object* v_toPure_1277_; lean_object* v___f_1278_; lean_object* v___f_1279_; uint8_t v___x_1280_; lean_object* v___x_1281_; lean_object* v___f_1282_; lean_object* v___f_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v_toApplicative_1275_ = lean_ctor_get(v_inst_1271_, 0);
lean_inc_ref(v_toApplicative_1275_);
v_toBind_1276_ = lean_ctor_get(v_inst_1271_, 1);
lean_inc(v_toBind_1276_);
lean_dec_ref(v_inst_1271_);
v_toPure_1277_ = lean_ctor_get(v_toApplicative_1275_, 1);
lean_inc(v_toPure_1277_);
lean_dec_ref(v_toApplicative_1275_);
lean_inc(v_toBind_1276_);
v___f_1278_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1278_, 0, v_toBind_1276_);
lean_inc(v_toPure_1277_);
v___f_1279_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1279_, 0, v_toPure_1277_);
v___x_1280_ = 1;
v___x_1281_ = lean_box(v___x_1280_);
v___f_1282_ = lean_alloc_closure((void*)(l_Std_IterM_allM___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1282_, 0, v_toPure_1277_);
lean_closure_set(v___f_1282_, 1, v___x_1281_);
v___f_1283_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1283_, 0, v_p_1273_);
lean_closure_set(v___f_1283_, 1, v_toBind_1276_);
lean_closure_set(v___f_1283_, 2, v___f_1282_);
lean_closure_set(v___f_1283_, 3, v___f_1279_);
v___x_1284_ = lean_box(v___x_1280_);
v___x_1285_ = lean_apply_6(v_inst_1272_, v___f_1278_, lean_box(0), lean_box(0), v_it_1274_, v___x_1284_, v___f_1283_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM(lean_object* v_00_u03b1_1286_, lean_object* v_00_u03b2_1287_, lean_object* v_m_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_p_1292_, lean_object* v_it_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Std_IterM_allM___redArg(v_inst_1289_, v_inst_1291_, v_p_1292_, v_it_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM___boxed(lean_object* v_00_u03b1_1295_, lean_object* v_00_u03b2_1296_, lean_object* v_m_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_p_1301_, lean_object* v_it_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Std_IterM_allM(v_00_u03b1_1295_, v_00_u03b2_1296_, v_m_1297_, v_inst_1298_, v_inst_1299_, v_inst_1300_, v_p_1301_, v_it_1302_);
lean_dec(v_inst_1299_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM___redArg(lean_object* v_inst_1304_, lean_object* v_inst_1305_, lean_object* v_p_1306_, lean_object* v_it_1307_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Std_IterM_allM___redArg(v_inst_1304_, v_inst_1305_, v_p_1306_, v_it_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM(lean_object* v_00_u03b1_1309_, lean_object* v_00_u03b2_1310_, lean_object* v_m_1311_, lean_object* v_inst_1312_, lean_object* v_inst_1313_, lean_object* v_inst_1314_, lean_object* v_p_1315_, lean_object* v_it_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Std_IterM_allM___redArg(v_inst_1312_, v_inst_1314_, v_p_1315_, v_it_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM___boxed(lean_object* v_00_u03b1_1318_, lean_object* v_00_u03b2_1319_, lean_object* v_m_1320_, lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_p_1324_, lean_object* v_it_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Std_IterM_Partial_allM(v_00_u03b1_1318_, v_00_u03b2_1319_, v_m_1320_, v_inst_1321_, v_inst_1322_, v_inst_1323_, v_p_1324_, v_it_1325_);
lean_dec(v_inst_1322_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM___redArg(lean_object* v_inst_1327_, lean_object* v_inst_1328_, lean_object* v_p_1329_, lean_object* v_it_1330_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Std_IterM_allM___redArg(v_inst_1327_, v_inst_1328_, v_p_1329_, v_it_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM(lean_object* v_00_u03b1_1332_, lean_object* v_00_u03b2_1333_, lean_object* v_m_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_p_1339_, lean_object* v_it_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Std_IterM_allM___redArg(v_inst_1335_, v_inst_1337_, v_p_1339_, v_it_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM___boxed(lean_object* v_00_u03b1_1342_, lean_object* v_00_u03b2_1343_, lean_object* v_m_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_p_1349_, lean_object* v_it_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Std_IterM_Total_allM(v_00_u03b1_1342_, v_00_u03b2_1343_, v_m_1344_, v_inst_1345_, v_inst_1346_, v_inst_1347_, v_inst_1348_, v_p_1349_, v_it_1350_);
lean_dec(v_inst_1346_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_all___redArg(lean_object* v_inst_1352_, lean_object* v_inst_1353_, lean_object* v_p_1354_, lean_object* v_it_1355_){
_start:
{
lean_object* v_toApplicative_1356_; lean_object* v_toPure_1357_; lean_object* v___f_1358_; lean_object* v___x_1359_; 
v_toApplicative_1356_ = lean_ctor_get(v_inst_1352_, 0);
v_toPure_1357_ = lean_ctor_get(v_toApplicative_1356_, 1);
lean_inc(v_toPure_1357_);
v___f_1358_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1358_, 0, v_p_1354_);
lean_closure_set(v___f_1358_, 1, v_toPure_1357_);
v___x_1359_ = l_Std_IterM_allM___redArg(v_inst_1352_, v_inst_1353_, v___f_1358_, v_it_1355_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_all(lean_object* v_00_u03b1_1360_, lean_object* v_00_u03b2_1361_, lean_object* v_m_1362_, lean_object* v_inst_1363_, lean_object* v_inst_1364_, lean_object* v_inst_1365_, lean_object* v_p_1366_, lean_object* v_it_1367_){
_start:
{
lean_object* v_toApplicative_1368_; lean_object* v_toPure_1369_; lean_object* v___f_1370_; lean_object* v___x_1371_; 
v_toApplicative_1368_ = lean_ctor_get(v_inst_1363_, 0);
v_toPure_1369_ = lean_ctor_get(v_toApplicative_1368_, 1);
lean_inc(v_toPure_1369_);
v___f_1370_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1370_, 0, v_p_1366_);
lean_closure_set(v___f_1370_, 1, v_toPure_1369_);
v___x_1371_ = l_Std_IterM_allM___redArg(v_inst_1363_, v_inst_1365_, v___f_1370_, v_it_1367_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_all___boxed(lean_object* v_00_u03b1_1372_, lean_object* v_00_u03b2_1373_, lean_object* v_m_1374_, lean_object* v_inst_1375_, lean_object* v_inst_1376_, lean_object* v_inst_1377_, lean_object* v_p_1378_, lean_object* v_it_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Std_IterM_all(v_00_u03b1_1372_, v_00_u03b2_1373_, v_m_1374_, v_inst_1375_, v_inst_1376_, v_inst_1377_, v_p_1378_, v_it_1379_);
lean_dec(v_inst_1376_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all___redArg(lean_object* v_inst_1381_, lean_object* v_inst_1382_, lean_object* v_p_1383_, lean_object* v_it_1384_){
_start:
{
lean_object* v_toApplicative_1385_; lean_object* v_toPure_1386_; lean_object* v___f_1387_; lean_object* v___x_1388_; 
v_toApplicative_1385_ = lean_ctor_get(v_inst_1381_, 0);
v_toPure_1386_ = lean_ctor_get(v_toApplicative_1385_, 1);
lean_inc(v_toPure_1386_);
v___f_1387_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1387_, 0, v_p_1383_);
lean_closure_set(v___f_1387_, 1, v_toPure_1386_);
v___x_1388_ = l_Std_IterM_allM___redArg(v_inst_1381_, v_inst_1382_, v___f_1387_, v_it_1384_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all(lean_object* v_00_u03b1_1389_, lean_object* v_00_u03b2_1390_, lean_object* v_m_1391_, lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_inst_1394_, lean_object* v_p_1395_, lean_object* v_it_1396_){
_start:
{
lean_object* v_toApplicative_1397_; lean_object* v_toPure_1398_; lean_object* v___f_1399_; lean_object* v___x_1400_; 
v_toApplicative_1397_ = lean_ctor_get(v_inst_1392_, 0);
v_toPure_1398_ = lean_ctor_get(v_toApplicative_1397_, 1);
lean_inc(v_toPure_1398_);
v___f_1399_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1399_, 0, v_p_1395_);
lean_closure_set(v___f_1399_, 1, v_toPure_1398_);
v___x_1400_ = l_Std_IterM_allM___redArg(v_inst_1392_, v_inst_1394_, v___f_1399_, v_it_1396_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all___boxed(lean_object* v_00_u03b1_1401_, lean_object* v_00_u03b2_1402_, lean_object* v_m_1403_, lean_object* v_inst_1404_, lean_object* v_inst_1405_, lean_object* v_inst_1406_, lean_object* v_p_1407_, lean_object* v_it_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Std_IterM_Partial_all(v_00_u03b1_1401_, v_00_u03b2_1402_, v_m_1403_, v_inst_1404_, v_inst_1405_, v_inst_1406_, v_p_1407_, v_it_1408_);
lean_dec(v_inst_1405_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_all___redArg(lean_object* v_inst_1410_, lean_object* v_inst_1411_, lean_object* v_p_1412_, lean_object* v_it_1413_){
_start:
{
lean_object* v_toApplicative_1414_; lean_object* v_toPure_1415_; lean_object* v___f_1416_; lean_object* v___x_1417_; 
v_toApplicative_1414_ = lean_ctor_get(v_inst_1410_, 0);
v_toPure_1415_ = lean_ctor_get(v_toApplicative_1414_, 1);
lean_inc(v_toPure_1415_);
v___f_1416_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1416_, 0, v_p_1412_);
lean_closure_set(v___f_1416_, 1, v_toPure_1415_);
v___x_1417_ = l_Std_IterM_allM___redArg(v_inst_1410_, v_inst_1411_, v___f_1416_, v_it_1413_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_all(lean_object* v_00_u03b1_1418_, lean_object* v_00_u03b2_1419_, lean_object* v_m_1420_, lean_object* v_inst_1421_, lean_object* v_inst_1422_, lean_object* v_inst_1423_, lean_object* v_inst_1424_, lean_object* v_p_1425_, lean_object* v_it_1426_){
_start:
{
lean_object* v_toApplicative_1427_; lean_object* v_toPure_1428_; lean_object* v___f_1429_; lean_object* v___x_1430_; 
v_toApplicative_1427_ = lean_ctor_get(v_inst_1421_, 0);
v_toPure_1428_ = lean_ctor_get(v_toApplicative_1427_, 1);
lean_inc(v_toPure_1428_);
v___f_1429_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1429_, 0, v_p_1425_);
lean_closure_set(v___f_1429_, 1, v_toPure_1428_);
v___x_1430_ = l_Std_IterM_allM___redArg(v_inst_1421_, v_inst_1423_, v___f_1429_, v_it_1426_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_all___boxed(lean_object* v_00_u03b1_1431_, lean_object* v_00_u03b2_1432_, lean_object* v_m_1433_, lean_object* v_inst_1434_, lean_object* v_inst_1435_, lean_object* v_inst_1436_, lean_object* v_inst_1437_, lean_object* v_p_1438_, lean_object* v_it_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Std_IterM_Total_all(v_00_u03b1_1431_, v_00_u03b2_1432_, v_m_1433_, v_inst_1434_, v_inst_1435_, v_inst_1436_, v_inst_1437_, v_p_1438_, v_it_1439_);
lean_dec(v_inst_1435_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__1(lean_object* v_toPure_1441_, lean_object* v_____do__lift_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_apply_2(v_toPure_1441_, lean_box(0), v_____do__lift_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__0(lean_object* v___x_1444_, lean_object* v_toPure_1445_, lean_object* v_____do__lift_1446_){
_start:
{
if (lean_obj_tag(v_____do__lift_1446_) == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1444_);
v___x_1448_ = lean_apply_2(v_toPure_1445_, lean_box(0), v___x_1447_);
return v___x_1448_;
}
else
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_dec(v___x_1444_);
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v_____do__lift_1446_);
v___x_1450_ = lean_apply_2(v_toPure_1445_, lean_box(0), v___x_1449_);
return v___x_1450_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__2(lean_object* v_f_1451_, lean_object* v_toBind_1452_, lean_object* v___f_1453_, lean_object* v___f_1454_, lean_object* v_x1_1455_, lean_object* v_x2_1456_, lean_object* v_x3_1457_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = lean_apply_1(v_f_1451_, v_x1_1455_);
lean_inc(v_toBind_1452_);
v___x_1459_ = lean_apply_4(v_toBind_1452_, lean_box(0), lean_box(0), v___x_1458_, v___f_1453_);
v___x_1460_ = lean_apply_4(v_toBind_1452_, lean_box(0), lean_box(0), v___x_1459_, v___f_1454_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed(lean_object* v_f_1461_, lean_object* v_toBind_1462_, lean_object* v___f_1463_, lean_object* v___f_1464_, lean_object* v_x1_1465_, lean_object* v_x2_1466_, lean_object* v_x3_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Std_IterM_findSomeM_x3f___redArg___lam__2(v_f_1461_, v_toBind_1462_, v___f_1463_, v___f_1464_, v_x1_1465_, v_x2_1466_, v_x3_1467_);
lean_dec(v_x3_1467_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg(lean_object* v_inst_1469_, lean_object* v_inst_1470_, lean_object* v_it_1471_, lean_object* v_f_1472_){
_start:
{
lean_object* v_toApplicative_1473_; lean_object* v_toBind_1474_; lean_object* v_toPure_1475_; lean_object* v___f_1476_; lean_object* v___f_1477_; lean_object* v___x_1478_; lean_object* v___f_1479_; lean_object* v___f_1480_; lean_object* v___x_1481_; 
v_toApplicative_1473_ = lean_ctor_get(v_inst_1469_, 0);
lean_inc_ref(v_toApplicative_1473_);
v_toBind_1474_ = lean_ctor_get(v_inst_1469_, 1);
lean_inc(v_toBind_1474_);
lean_dec_ref(v_inst_1469_);
v_toPure_1475_ = lean_ctor_get(v_toApplicative_1473_, 1);
lean_inc(v_toPure_1475_);
lean_dec_ref(v_toApplicative_1473_);
lean_inc(v_toBind_1474_);
v___f_1476_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1476_, 0, v_toBind_1474_);
lean_inc(v_toPure_1475_);
v___f_1477_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1477_, 0, v_toPure_1475_);
v___x_1478_ = lean_box(0);
v___f_1479_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1479_, 0, v___x_1478_);
lean_closure_set(v___f_1479_, 1, v_toPure_1475_);
v___f_1480_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1480_, 0, v_f_1472_);
lean_closure_set(v___f_1480_, 1, v_toBind_1474_);
lean_closure_set(v___f_1480_, 2, v___f_1479_);
lean_closure_set(v___f_1480_, 3, v___f_1477_);
v___x_1481_ = lean_apply_6(v_inst_1470_, v___f_1476_, lean_box(0), lean_box(0), v_it_1471_, v___x_1478_, v___f_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f(lean_object* v_00_u03b1_1482_, lean_object* v_00_u03b2_1483_, lean_object* v_00_u03b3_1484_, lean_object* v_m_1485_, lean_object* v_inst_1486_, lean_object* v_inst_1487_, lean_object* v_inst_1488_, lean_object* v_it_1489_, lean_object* v_f_1490_){
_start:
{
lean_object* v_toApplicative_1491_; lean_object* v_toBind_1492_; lean_object* v_toPure_1493_; lean_object* v___f_1494_; lean_object* v___f_1495_; lean_object* v___x_1496_; lean_object* v___f_1497_; lean_object* v___f_1498_; lean_object* v___x_1499_; 
v_toApplicative_1491_ = lean_ctor_get(v_inst_1486_, 0);
lean_inc_ref(v_toApplicative_1491_);
v_toBind_1492_ = lean_ctor_get(v_inst_1486_, 1);
lean_inc(v_toBind_1492_);
lean_dec_ref(v_inst_1486_);
v_toPure_1493_ = lean_ctor_get(v_toApplicative_1491_, 1);
lean_inc(v_toPure_1493_);
lean_dec_ref(v_toApplicative_1491_);
lean_inc(v_toBind_1492_);
v___f_1494_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1494_, 0, v_toBind_1492_);
lean_inc(v_toPure_1493_);
v___f_1495_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1495_, 0, v_toPure_1493_);
v___x_1496_ = lean_box(0);
v___f_1497_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1497_, 0, v___x_1496_);
lean_closure_set(v___f_1497_, 1, v_toPure_1493_);
v___f_1498_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1498_, 0, v_f_1490_);
lean_closure_set(v___f_1498_, 1, v_toBind_1492_);
lean_closure_set(v___f_1498_, 2, v___f_1497_);
lean_closure_set(v___f_1498_, 3, v___f_1495_);
v___x_1499_ = lean_apply_6(v_inst_1488_, v___f_1494_, lean_box(0), lean_box(0), v_it_1489_, v___x_1496_, v___f_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___boxed(lean_object* v_00_u03b1_1500_, lean_object* v_00_u03b2_1501_, lean_object* v_00_u03b3_1502_, lean_object* v_m_1503_, lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_inst_1506_, lean_object* v_it_1507_, lean_object* v_f_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Std_IterM_findSomeM_x3f(v_00_u03b1_1500_, v_00_u03b2_1501_, v_00_u03b3_1502_, v_m_1503_, v_inst_1504_, v_inst_1505_, v_inst_1506_, v_it_1507_, v_f_1508_);
lean_dec(v_inst_1505_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f___redArg(lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v_it_1512_, lean_object* v_f_1513_){
_start:
{
lean_object* v_toApplicative_1514_; lean_object* v_toBind_1515_; lean_object* v_toPure_1516_; lean_object* v___f_1517_; lean_object* v___f_1518_; lean_object* v___x_1519_; lean_object* v___f_1520_; lean_object* v___f_1521_; lean_object* v___x_1522_; 
v_toApplicative_1514_ = lean_ctor_get(v_inst_1510_, 0);
lean_inc_ref(v_toApplicative_1514_);
v_toBind_1515_ = lean_ctor_get(v_inst_1510_, 1);
lean_inc(v_toBind_1515_);
lean_dec_ref(v_inst_1510_);
v_toPure_1516_ = lean_ctor_get(v_toApplicative_1514_, 1);
lean_inc(v_toPure_1516_);
lean_dec_ref(v_toApplicative_1514_);
lean_inc(v_toBind_1515_);
v___f_1517_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1517_, 0, v_toBind_1515_);
lean_inc(v_toPure_1516_);
v___f_1518_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1518_, 0, v_toPure_1516_);
v___x_1519_ = lean_box(0);
v___f_1520_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1520_, 0, v___x_1519_);
lean_closure_set(v___f_1520_, 1, v_toPure_1516_);
v___f_1521_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1521_, 0, v_f_1513_);
lean_closure_set(v___f_1521_, 1, v_toBind_1515_);
lean_closure_set(v___f_1521_, 2, v___f_1520_);
lean_closure_set(v___f_1521_, 3, v___f_1518_);
v___x_1522_ = lean_apply_6(v_inst_1511_, v___f_1517_, lean_box(0), lean_box(0), v_it_1512_, v___x_1519_, v___f_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f(lean_object* v_00_u03b1_1523_, lean_object* v_00_u03b2_1524_, lean_object* v_00_u03b3_1525_, lean_object* v_m_1526_, lean_object* v_inst_1527_, lean_object* v_inst_1528_, lean_object* v_inst_1529_, lean_object* v_it_1530_, lean_object* v_f_1531_){
_start:
{
lean_object* v_toApplicative_1532_; lean_object* v_toBind_1533_; lean_object* v_toPure_1534_; lean_object* v___f_1535_; lean_object* v___f_1536_; lean_object* v___x_1537_; lean_object* v___f_1538_; lean_object* v___f_1539_; lean_object* v___x_1540_; 
v_toApplicative_1532_ = lean_ctor_get(v_inst_1527_, 0);
lean_inc_ref(v_toApplicative_1532_);
v_toBind_1533_ = lean_ctor_get(v_inst_1527_, 1);
lean_inc(v_toBind_1533_);
lean_dec_ref(v_inst_1527_);
v_toPure_1534_ = lean_ctor_get(v_toApplicative_1532_, 1);
lean_inc(v_toPure_1534_);
lean_dec_ref(v_toApplicative_1532_);
lean_inc(v_toBind_1533_);
v___f_1535_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1535_, 0, v_toBind_1533_);
lean_inc(v_toPure_1534_);
v___f_1536_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1536_, 0, v_toPure_1534_);
v___x_1537_ = lean_box(0);
v___f_1538_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1538_, 0, v___x_1537_);
lean_closure_set(v___f_1538_, 1, v_toPure_1534_);
v___f_1539_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1539_, 0, v_f_1531_);
lean_closure_set(v___f_1539_, 1, v_toBind_1533_);
lean_closure_set(v___f_1539_, 2, v___f_1538_);
lean_closure_set(v___f_1539_, 3, v___f_1536_);
v___x_1540_ = lean_apply_6(v_inst_1529_, v___f_1535_, lean_box(0), lean_box(0), v_it_1530_, v___x_1537_, v___f_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f___boxed(lean_object* v_00_u03b1_1541_, lean_object* v_00_u03b2_1542_, lean_object* v_00_u03b3_1543_, lean_object* v_m_1544_, lean_object* v_inst_1545_, lean_object* v_inst_1546_, lean_object* v_inst_1547_, lean_object* v_it_1548_, lean_object* v_f_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Std_IterM_Partial_findSomeM_x3f(v_00_u03b1_1541_, v_00_u03b2_1542_, v_00_u03b3_1543_, v_m_1544_, v_inst_1545_, v_inst_1546_, v_inst_1547_, v_it_1548_, v_f_1549_);
lean_dec(v_inst_1546_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f___redArg(lean_object* v_inst_1551_, lean_object* v_inst_1552_, lean_object* v_it_1553_, lean_object* v_f_1554_){
_start:
{
lean_object* v_toApplicative_1555_; lean_object* v_toBind_1556_; lean_object* v_toPure_1557_; lean_object* v___f_1558_; lean_object* v___f_1559_; lean_object* v___x_1560_; lean_object* v___f_1561_; lean_object* v___f_1562_; lean_object* v___x_1563_; 
v_toApplicative_1555_ = lean_ctor_get(v_inst_1551_, 0);
lean_inc_ref(v_toApplicative_1555_);
v_toBind_1556_ = lean_ctor_get(v_inst_1551_, 1);
lean_inc(v_toBind_1556_);
lean_dec_ref(v_inst_1551_);
v_toPure_1557_ = lean_ctor_get(v_toApplicative_1555_, 1);
lean_inc(v_toPure_1557_);
lean_dec_ref(v_toApplicative_1555_);
lean_inc(v_toBind_1556_);
v___f_1558_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1558_, 0, v_toBind_1556_);
lean_inc(v_toPure_1557_);
v___f_1559_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1559_, 0, v_toPure_1557_);
v___x_1560_ = lean_box(0);
v___f_1561_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1561_, 0, v___x_1560_);
lean_closure_set(v___f_1561_, 1, v_toPure_1557_);
v___f_1562_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1562_, 0, v_f_1554_);
lean_closure_set(v___f_1562_, 1, v_toBind_1556_);
lean_closure_set(v___f_1562_, 2, v___f_1561_);
lean_closure_set(v___f_1562_, 3, v___f_1559_);
v___x_1563_ = lean_apply_6(v_inst_1552_, v___f_1558_, lean_box(0), lean_box(0), v_it_1553_, v___x_1560_, v___f_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f(lean_object* v_00_u03b1_1564_, lean_object* v_00_u03b2_1565_, lean_object* v_00_u03b3_1566_, lean_object* v_m_1567_, lean_object* v_inst_1568_, lean_object* v_inst_1569_, lean_object* v_inst_1570_, lean_object* v_inst_1571_, lean_object* v_it_1572_, lean_object* v_f_1573_){
_start:
{
lean_object* v_toApplicative_1574_; lean_object* v_toBind_1575_; lean_object* v_toPure_1576_; lean_object* v___f_1577_; lean_object* v___f_1578_; lean_object* v___x_1579_; lean_object* v___f_1580_; lean_object* v___f_1581_; lean_object* v___x_1582_; 
v_toApplicative_1574_ = lean_ctor_get(v_inst_1568_, 0);
lean_inc_ref(v_toApplicative_1574_);
v_toBind_1575_ = lean_ctor_get(v_inst_1568_, 1);
lean_inc(v_toBind_1575_);
lean_dec_ref(v_inst_1568_);
v_toPure_1576_ = lean_ctor_get(v_toApplicative_1574_, 1);
lean_inc(v_toPure_1576_);
lean_dec_ref(v_toApplicative_1574_);
lean_inc(v_toBind_1575_);
v___f_1577_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1577_, 0, v_toBind_1575_);
lean_inc(v_toPure_1576_);
v___f_1578_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1578_, 0, v_toPure_1576_);
v___x_1579_ = lean_box(0);
v___f_1580_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1580_, 0, v___x_1579_);
lean_closure_set(v___f_1580_, 1, v_toPure_1576_);
v___f_1581_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1581_, 0, v_f_1573_);
lean_closure_set(v___f_1581_, 1, v_toBind_1575_);
lean_closure_set(v___f_1581_, 2, v___f_1580_);
lean_closure_set(v___f_1581_, 3, v___f_1578_);
v___x_1582_ = lean_apply_6(v_inst_1570_, v___f_1577_, lean_box(0), lean_box(0), v_it_1572_, v___x_1579_, v___f_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f___boxed(lean_object* v_00_u03b1_1583_, lean_object* v_00_u03b2_1584_, lean_object* v_00_u03b3_1585_, lean_object* v_m_1586_, lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_inst_1589_, lean_object* v_inst_1590_, lean_object* v_it_1591_, lean_object* v_f_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Std_IterM_Total_findSomeM_x3f(v_00_u03b1_1583_, v_00_u03b2_1584_, v_00_u03b3_1585_, v_m_1586_, v_inst_1587_, v_inst_1588_, v_inst_1589_, v_inst_1590_, v_it_1591_, v_f_1592_);
lean_dec(v_inst_1588_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg___lam__3(lean_object* v_f_1594_, lean_object* v_toPure_1595_, lean_object* v_toBind_1596_, lean_object* v___f_1597_, lean_object* v___f_1598_, lean_object* v_x1_1599_, lean_object* v_x2_1600_, lean_object* v_x3_1601_){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1602_ = lean_apply_1(v_f_1594_, v_x1_1599_);
v___x_1603_ = lean_apply_2(v_toPure_1595_, lean_box(0), v___x_1602_);
lean_inc(v_toBind_1596_);
v___x_1604_ = lean_apply_4(v_toBind_1596_, lean_box(0), lean_box(0), v___x_1603_, v___f_1597_);
v___x_1605_ = lean_apply_4(v_toBind_1596_, lean_box(0), lean_box(0), v___x_1604_, v___f_1598_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg___lam__3___boxed(lean_object* v_f_1606_, lean_object* v_toPure_1607_, lean_object* v_toBind_1608_, lean_object* v___f_1609_, lean_object* v___f_1610_, lean_object* v_x1_1611_, lean_object* v_x2_1612_, lean_object* v_x3_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Std_IterM_findSome_x3f___redArg___lam__3(v_f_1606_, v_toPure_1607_, v_toBind_1608_, v___f_1609_, v___f_1610_, v_x1_1611_, v_x2_1612_, v_x3_1613_);
lean_dec(v_x3_1613_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg(lean_object* v_inst_1615_, lean_object* v_inst_1616_, lean_object* v_it_1617_, lean_object* v_f_1618_){
_start:
{
lean_object* v_toApplicative_1619_; lean_object* v_toBind_1620_; lean_object* v_toPure_1621_; lean_object* v___f_1622_; lean_object* v___f_1623_; lean_object* v___x_1624_; lean_object* v___f_1625_; lean_object* v___f_1626_; lean_object* v___x_1627_; 
v_toApplicative_1619_ = lean_ctor_get(v_inst_1615_, 0);
lean_inc_ref(v_toApplicative_1619_);
v_toBind_1620_ = lean_ctor_get(v_inst_1615_, 1);
lean_inc(v_toBind_1620_);
lean_dec_ref(v_inst_1615_);
v_toPure_1621_ = lean_ctor_get(v_toApplicative_1619_, 1);
lean_inc(v_toPure_1621_);
lean_dec_ref(v_toApplicative_1619_);
lean_inc(v_toBind_1620_);
v___f_1622_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1622_, 0, v_toBind_1620_);
lean_inc(v_toPure_1621_);
v___f_1623_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1623_, 0, v_toPure_1621_);
v___x_1624_ = lean_box(0);
lean_inc(v_toPure_1621_);
v___f_1625_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1625_, 0, v___x_1624_);
lean_closure_set(v___f_1625_, 1, v_toPure_1621_);
v___f_1626_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1626_, 0, v_f_1618_);
lean_closure_set(v___f_1626_, 1, v_toPure_1621_);
lean_closure_set(v___f_1626_, 2, v_toBind_1620_);
lean_closure_set(v___f_1626_, 3, v___f_1625_);
lean_closure_set(v___f_1626_, 4, v___f_1623_);
v___x_1627_ = lean_apply_6(v_inst_1616_, v___f_1622_, lean_box(0), lean_box(0), v_it_1617_, v___x_1624_, v___f_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f(lean_object* v_00_u03b1_1628_, lean_object* v_00_u03b2_1629_, lean_object* v_00_u03b3_1630_, lean_object* v_m_1631_, lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_inst_1634_, lean_object* v_it_1635_, lean_object* v_f_1636_){
_start:
{
lean_object* v_toApplicative_1637_; lean_object* v_toBind_1638_; lean_object* v_toPure_1639_; lean_object* v___f_1640_; lean_object* v___f_1641_; lean_object* v___x_1642_; lean_object* v___f_1643_; lean_object* v___f_1644_; lean_object* v___x_1645_; 
v_toApplicative_1637_ = lean_ctor_get(v_inst_1632_, 0);
lean_inc_ref(v_toApplicative_1637_);
v_toBind_1638_ = lean_ctor_get(v_inst_1632_, 1);
lean_inc(v_toBind_1638_);
lean_dec_ref(v_inst_1632_);
v_toPure_1639_ = lean_ctor_get(v_toApplicative_1637_, 1);
lean_inc(v_toPure_1639_);
lean_dec_ref(v_toApplicative_1637_);
lean_inc(v_toBind_1638_);
v___f_1640_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1640_, 0, v_toBind_1638_);
lean_inc(v_toPure_1639_);
v___f_1641_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1641_, 0, v_toPure_1639_);
v___x_1642_ = lean_box(0);
lean_inc(v_toPure_1639_);
v___f_1643_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1643_, 0, v___x_1642_);
lean_closure_set(v___f_1643_, 1, v_toPure_1639_);
v___f_1644_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1644_, 0, v_f_1636_);
lean_closure_set(v___f_1644_, 1, v_toPure_1639_);
lean_closure_set(v___f_1644_, 2, v_toBind_1638_);
lean_closure_set(v___f_1644_, 3, v___f_1643_);
lean_closure_set(v___f_1644_, 4, v___f_1641_);
v___x_1645_ = lean_apply_6(v_inst_1634_, v___f_1640_, lean_box(0), lean_box(0), v_it_1635_, v___x_1642_, v___f_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___boxed(lean_object* v_00_u03b1_1646_, lean_object* v_00_u03b2_1647_, lean_object* v_00_u03b3_1648_, lean_object* v_m_1649_, lean_object* v_inst_1650_, lean_object* v_inst_1651_, lean_object* v_inst_1652_, lean_object* v_it_1653_, lean_object* v_f_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Std_IterM_findSome_x3f(v_00_u03b1_1646_, v_00_u03b2_1647_, v_00_u03b3_1648_, v_m_1649_, v_inst_1650_, v_inst_1651_, v_inst_1652_, v_it_1653_, v_f_1654_);
lean_dec(v_inst_1651_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f___redArg(lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_it_1658_, lean_object* v_f_1659_){
_start:
{
lean_object* v_toApplicative_1660_; lean_object* v_toBind_1661_; lean_object* v_toPure_1662_; lean_object* v___f_1663_; lean_object* v___f_1664_; lean_object* v___x_1665_; lean_object* v___f_1666_; lean_object* v___f_1667_; lean_object* v___x_1668_; 
v_toApplicative_1660_ = lean_ctor_get(v_inst_1656_, 0);
lean_inc_ref(v_toApplicative_1660_);
v_toBind_1661_ = lean_ctor_get(v_inst_1656_, 1);
lean_inc(v_toBind_1661_);
lean_dec_ref(v_inst_1656_);
v_toPure_1662_ = lean_ctor_get(v_toApplicative_1660_, 1);
lean_inc(v_toPure_1662_);
lean_dec_ref(v_toApplicative_1660_);
lean_inc(v_toBind_1661_);
v___f_1663_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1663_, 0, v_toBind_1661_);
lean_inc(v_toPure_1662_);
v___f_1664_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1664_, 0, v_toPure_1662_);
v___x_1665_ = lean_box(0);
lean_inc(v_toPure_1662_);
v___f_1666_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1666_, 0, v___x_1665_);
lean_closure_set(v___f_1666_, 1, v_toPure_1662_);
v___f_1667_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1667_, 0, v_f_1659_);
lean_closure_set(v___f_1667_, 1, v_toPure_1662_);
lean_closure_set(v___f_1667_, 2, v_toBind_1661_);
lean_closure_set(v___f_1667_, 3, v___f_1666_);
lean_closure_set(v___f_1667_, 4, v___f_1664_);
v___x_1668_ = lean_apply_6(v_inst_1657_, v___f_1663_, lean_box(0), lean_box(0), v_it_1658_, v___x_1665_, v___f_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f(lean_object* v_00_u03b1_1669_, lean_object* v_00_u03b2_1670_, lean_object* v_00_u03b3_1671_, lean_object* v_m_1672_, lean_object* v_inst_1673_, lean_object* v_inst_1674_, lean_object* v_inst_1675_, lean_object* v_it_1676_, lean_object* v_f_1677_){
_start:
{
lean_object* v_toApplicative_1678_; lean_object* v_toBind_1679_; lean_object* v_toPure_1680_; lean_object* v___f_1681_; lean_object* v___f_1682_; lean_object* v___x_1683_; lean_object* v___f_1684_; lean_object* v___f_1685_; lean_object* v___x_1686_; 
v_toApplicative_1678_ = lean_ctor_get(v_inst_1673_, 0);
lean_inc_ref(v_toApplicative_1678_);
v_toBind_1679_ = lean_ctor_get(v_inst_1673_, 1);
lean_inc(v_toBind_1679_);
lean_dec_ref(v_inst_1673_);
v_toPure_1680_ = lean_ctor_get(v_toApplicative_1678_, 1);
lean_inc(v_toPure_1680_);
lean_dec_ref(v_toApplicative_1678_);
lean_inc(v_toBind_1679_);
v___f_1681_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1681_, 0, v_toBind_1679_);
lean_inc(v_toPure_1680_);
v___f_1682_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1682_, 0, v_toPure_1680_);
v___x_1683_ = lean_box(0);
lean_inc(v_toPure_1680_);
v___f_1684_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1684_, 0, v___x_1683_);
lean_closure_set(v___f_1684_, 1, v_toPure_1680_);
v___f_1685_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1685_, 0, v_f_1677_);
lean_closure_set(v___f_1685_, 1, v_toPure_1680_);
lean_closure_set(v___f_1685_, 2, v_toBind_1679_);
lean_closure_set(v___f_1685_, 3, v___f_1684_);
lean_closure_set(v___f_1685_, 4, v___f_1682_);
v___x_1686_ = lean_apply_6(v_inst_1675_, v___f_1681_, lean_box(0), lean_box(0), v_it_1676_, v___x_1683_, v___f_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f___boxed(lean_object* v_00_u03b1_1687_, lean_object* v_00_u03b2_1688_, lean_object* v_00_u03b3_1689_, lean_object* v_m_1690_, lean_object* v_inst_1691_, lean_object* v_inst_1692_, lean_object* v_inst_1693_, lean_object* v_it_1694_, lean_object* v_f_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Std_IterM_Partial_findSome_x3f(v_00_u03b1_1687_, v_00_u03b2_1688_, v_00_u03b3_1689_, v_m_1690_, v_inst_1691_, v_inst_1692_, v_inst_1693_, v_it_1694_, v_f_1695_);
lean_dec(v_inst_1692_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f___redArg(lean_object* v_inst_1697_, lean_object* v_inst_1698_, lean_object* v_it_1699_, lean_object* v_f_1700_){
_start:
{
lean_object* v_toApplicative_1701_; lean_object* v_toBind_1702_; lean_object* v_toPure_1703_; lean_object* v___f_1704_; lean_object* v___f_1705_; lean_object* v___x_1706_; lean_object* v___f_1707_; lean_object* v___f_1708_; lean_object* v___x_1709_; 
v_toApplicative_1701_ = lean_ctor_get(v_inst_1697_, 0);
lean_inc_ref(v_toApplicative_1701_);
v_toBind_1702_ = lean_ctor_get(v_inst_1697_, 1);
lean_inc(v_toBind_1702_);
lean_dec_ref(v_inst_1697_);
v_toPure_1703_ = lean_ctor_get(v_toApplicative_1701_, 1);
lean_inc(v_toPure_1703_);
lean_dec_ref(v_toApplicative_1701_);
lean_inc(v_toBind_1702_);
v___f_1704_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1704_, 0, v_toBind_1702_);
lean_inc(v_toPure_1703_);
v___f_1705_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1705_, 0, v_toPure_1703_);
v___x_1706_ = lean_box(0);
lean_inc(v_toPure_1703_);
v___f_1707_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1707_, 0, v___x_1706_);
lean_closure_set(v___f_1707_, 1, v_toPure_1703_);
v___f_1708_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1708_, 0, v_f_1700_);
lean_closure_set(v___f_1708_, 1, v_toPure_1703_);
lean_closure_set(v___f_1708_, 2, v_toBind_1702_);
lean_closure_set(v___f_1708_, 3, v___f_1707_);
lean_closure_set(v___f_1708_, 4, v___f_1705_);
v___x_1709_ = lean_apply_6(v_inst_1698_, v___f_1704_, lean_box(0), lean_box(0), v_it_1699_, v___x_1706_, v___f_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f(lean_object* v_00_u03b1_1710_, lean_object* v_00_u03b2_1711_, lean_object* v_00_u03b3_1712_, lean_object* v_m_1713_, lean_object* v_inst_1714_, lean_object* v_inst_1715_, lean_object* v_inst_1716_, lean_object* v_inst_1717_, lean_object* v_it_1718_, lean_object* v_f_1719_){
_start:
{
lean_object* v_toApplicative_1720_; lean_object* v_toBind_1721_; lean_object* v_toPure_1722_; lean_object* v___f_1723_; lean_object* v___f_1724_; lean_object* v___x_1725_; lean_object* v___f_1726_; lean_object* v___f_1727_; lean_object* v___x_1728_; 
v_toApplicative_1720_ = lean_ctor_get(v_inst_1714_, 0);
lean_inc_ref(v_toApplicative_1720_);
v_toBind_1721_ = lean_ctor_get(v_inst_1714_, 1);
lean_inc(v_toBind_1721_);
lean_dec_ref(v_inst_1714_);
v_toPure_1722_ = lean_ctor_get(v_toApplicative_1720_, 1);
lean_inc(v_toPure_1722_);
lean_dec_ref(v_toApplicative_1720_);
lean_inc(v_toBind_1721_);
v___f_1723_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1723_, 0, v_toBind_1721_);
lean_inc(v_toPure_1722_);
v___f_1724_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1724_, 0, v_toPure_1722_);
v___x_1725_ = lean_box(0);
lean_inc(v_toPure_1722_);
v___f_1726_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1726_, 0, v___x_1725_);
lean_closure_set(v___f_1726_, 1, v_toPure_1722_);
v___f_1727_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1727_, 0, v_f_1719_);
lean_closure_set(v___f_1727_, 1, v_toPure_1722_);
lean_closure_set(v___f_1727_, 2, v_toBind_1721_);
lean_closure_set(v___f_1727_, 3, v___f_1726_);
lean_closure_set(v___f_1727_, 4, v___f_1724_);
v___x_1728_ = lean_apply_6(v_inst_1716_, v___f_1723_, lean_box(0), lean_box(0), v_it_1718_, v___x_1725_, v___f_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f___boxed(lean_object* v_00_u03b1_1729_, lean_object* v_00_u03b2_1730_, lean_object* v_00_u03b3_1731_, lean_object* v_m_1732_, lean_object* v_inst_1733_, lean_object* v_inst_1734_, lean_object* v_inst_1735_, lean_object* v_inst_1736_, lean_object* v_it_1737_, lean_object* v_f_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Std_IterM_Total_findSome_x3f(v_00_u03b1_1729_, v_00_u03b2_1730_, v_00_u03b3_1731_, v_m_1732_, v_inst_1733_, v_inst_1734_, v_inst_1735_, v_inst_1736_, v_it_1737_, v_f_1738_);
lean_dec(v_inst_1734_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__3(lean_object* v_toPure_1740_, lean_object* v___x_1741_, lean_object* v_x1_1742_, uint8_t v_____do__lift_1743_){
_start:
{
if (v_____do__lift_1743_ == 0)
{
lean_object* v___x_1744_; 
lean_dec(v_x1_1742_);
v___x_1744_ = lean_apply_2(v_toPure_1740_, lean_box(0), v___x_1741_);
return v___x_1744_;
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
lean_dec(v___x_1741_);
v___x_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_x1_1742_);
v___x_1746_ = lean_apply_2(v_toPure_1740_, lean_box(0), v___x_1745_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__3___boxed(lean_object* v_toPure_1747_, lean_object* v___x_1748_, lean_object* v_x1_1749_, lean_object* v_____do__lift_1750_){
_start:
{
uint8_t v_____do__lift_191__boxed_1751_; lean_object* v_res_1752_; 
v_____do__lift_191__boxed_1751_ = lean_unbox(v_____do__lift_1750_);
v_res_1752_ = l_Std_IterM_findM_x3f___redArg___lam__3(v_toPure_1747_, v___x_1748_, v_x1_1749_, v_____do__lift_191__boxed_1751_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__0(lean_object* v_toPure_1753_, lean_object* v___x_1754_, lean_object* v_f_1755_, lean_object* v_toBind_1756_, lean_object* v___f_1757_, lean_object* v___f_1758_, lean_object* v_x1_1759_, lean_object* v_x2_1760_, lean_object* v_x3_1761_){
_start:
{
lean_object* v___f_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_inc(v_x1_1759_);
v___f_1762_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_1762_, 0, v_toPure_1753_);
lean_closure_set(v___f_1762_, 1, v___x_1754_);
lean_closure_set(v___f_1762_, 2, v_x1_1759_);
v___x_1763_ = lean_apply_1(v_f_1755_, v_x1_1759_);
lean_inc(v_toBind_1756_);
v___x_1764_ = lean_apply_4(v_toBind_1756_, lean_box(0), lean_box(0), v___x_1763_, v___f_1762_);
lean_inc(v_toBind_1756_);
v___x_1765_ = lean_apply_4(v_toBind_1756_, lean_box(0), lean_box(0), v___x_1764_, v___f_1757_);
v___x_1766_ = lean_apply_4(v_toBind_1756_, lean_box(0), lean_box(0), v___x_1765_, v___f_1758_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_1767_, lean_object* v___x_1768_, lean_object* v_f_1769_, lean_object* v_toBind_1770_, lean_object* v___f_1771_, lean_object* v___f_1772_, lean_object* v_x1_1773_, lean_object* v_x2_1774_, lean_object* v_x3_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Std_IterM_findM_x3f___redArg___lam__0(v_toPure_1767_, v___x_1768_, v_f_1769_, v_toBind_1770_, v___f_1771_, v___f_1772_, v_x1_1773_, v_x2_1774_, v_x3_1775_);
lean_dec(v_x3_1775_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg(lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_it_1779_, lean_object* v_f_1780_){
_start:
{
lean_object* v_toApplicative_1781_; lean_object* v_toBind_1782_; lean_object* v_toPure_1783_; lean_object* v___f_1784_; lean_object* v___f_1785_; lean_object* v___x_1786_; lean_object* v___f_1787_; lean_object* v___f_1788_; lean_object* v___x_1789_; 
v_toApplicative_1781_ = lean_ctor_get(v_inst_1777_, 0);
lean_inc_ref(v_toApplicative_1781_);
v_toBind_1782_ = lean_ctor_get(v_inst_1777_, 1);
lean_inc(v_toBind_1782_);
lean_dec_ref(v_inst_1777_);
v_toPure_1783_ = lean_ctor_get(v_toApplicative_1781_, 1);
lean_inc(v_toPure_1783_);
lean_dec_ref(v_toApplicative_1781_);
lean_inc(v_toBind_1782_);
v___f_1784_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1784_, 0, v_toBind_1782_);
lean_inc(v_toPure_1783_);
v___f_1785_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1785_, 0, v_toPure_1783_);
v___x_1786_ = lean_box(0);
lean_inc(v_toPure_1783_);
v___f_1787_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1787_, 0, v___x_1786_);
lean_closure_set(v___f_1787_, 1, v_toPure_1783_);
v___f_1788_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1788_, 0, v_toPure_1783_);
lean_closure_set(v___f_1788_, 1, v___x_1786_);
lean_closure_set(v___f_1788_, 2, v_f_1780_);
lean_closure_set(v___f_1788_, 3, v_toBind_1782_);
lean_closure_set(v___f_1788_, 4, v___f_1787_);
lean_closure_set(v___f_1788_, 5, v___f_1785_);
v___x_1789_ = lean_apply_6(v_inst_1778_, v___f_1784_, lean_box(0), lean_box(0), v_it_1779_, v___x_1786_, v___f_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f(lean_object* v_00_u03b1_1790_, lean_object* v_00_u03b2_1791_, lean_object* v_m_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_it_1796_, lean_object* v_f_1797_){
_start:
{
lean_object* v_toApplicative_1798_; lean_object* v_toBind_1799_; lean_object* v_toPure_1800_; lean_object* v___f_1801_; lean_object* v___f_1802_; lean_object* v___x_1803_; lean_object* v___f_1804_; lean_object* v___f_1805_; lean_object* v___x_1806_; 
v_toApplicative_1798_ = lean_ctor_get(v_inst_1793_, 0);
lean_inc_ref(v_toApplicative_1798_);
v_toBind_1799_ = lean_ctor_get(v_inst_1793_, 1);
lean_inc(v_toBind_1799_);
lean_dec_ref(v_inst_1793_);
v_toPure_1800_ = lean_ctor_get(v_toApplicative_1798_, 1);
lean_inc(v_toPure_1800_);
lean_dec_ref(v_toApplicative_1798_);
lean_inc(v_toBind_1799_);
v___f_1801_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1801_, 0, v_toBind_1799_);
lean_inc(v_toPure_1800_);
v___f_1802_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1802_, 0, v_toPure_1800_);
v___x_1803_ = lean_box(0);
lean_inc(v_toPure_1800_);
v___f_1804_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1804_, 0, v___x_1803_);
lean_closure_set(v___f_1804_, 1, v_toPure_1800_);
v___f_1805_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1805_, 0, v_toPure_1800_);
lean_closure_set(v___f_1805_, 1, v___x_1803_);
lean_closure_set(v___f_1805_, 2, v_f_1797_);
lean_closure_set(v___f_1805_, 3, v_toBind_1799_);
lean_closure_set(v___f_1805_, 4, v___f_1804_);
lean_closure_set(v___f_1805_, 5, v___f_1802_);
v___x_1806_ = lean_apply_6(v_inst_1795_, v___f_1801_, lean_box(0), lean_box(0), v_it_1796_, v___x_1803_, v___f_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___boxed(lean_object* v_00_u03b1_1807_, lean_object* v_00_u03b2_1808_, lean_object* v_m_1809_, lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_inst_1812_, lean_object* v_it_1813_, lean_object* v_f_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Std_IterM_findM_x3f(v_00_u03b1_1807_, v_00_u03b2_1808_, v_m_1809_, v_inst_1810_, v_inst_1811_, v_inst_1812_, v_it_1813_, v_f_1814_);
lean_dec(v_inst_1811_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f___redArg(lean_object* v_inst_1816_, lean_object* v_inst_1817_, lean_object* v_it_1818_, lean_object* v_f_1819_){
_start:
{
lean_object* v_toApplicative_1820_; lean_object* v_toBind_1821_; lean_object* v_toPure_1822_; lean_object* v___f_1823_; lean_object* v___f_1824_; lean_object* v___x_1825_; lean_object* v___f_1826_; lean_object* v___f_1827_; lean_object* v___x_1828_; 
v_toApplicative_1820_ = lean_ctor_get(v_inst_1816_, 0);
lean_inc_ref(v_toApplicative_1820_);
v_toBind_1821_ = lean_ctor_get(v_inst_1816_, 1);
lean_inc(v_toBind_1821_);
lean_dec_ref(v_inst_1816_);
v_toPure_1822_ = lean_ctor_get(v_toApplicative_1820_, 1);
lean_inc(v_toPure_1822_);
lean_dec_ref(v_toApplicative_1820_);
lean_inc(v_toBind_1821_);
v___f_1823_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1823_, 0, v_toBind_1821_);
lean_inc(v_toPure_1822_);
v___f_1824_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1824_, 0, v_toPure_1822_);
v___x_1825_ = lean_box(0);
lean_inc(v_toPure_1822_);
v___f_1826_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1826_, 0, v___x_1825_);
lean_closure_set(v___f_1826_, 1, v_toPure_1822_);
v___f_1827_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1827_, 0, v_toPure_1822_);
lean_closure_set(v___f_1827_, 1, v___x_1825_);
lean_closure_set(v___f_1827_, 2, v_f_1819_);
lean_closure_set(v___f_1827_, 3, v_toBind_1821_);
lean_closure_set(v___f_1827_, 4, v___f_1826_);
lean_closure_set(v___f_1827_, 5, v___f_1824_);
v___x_1828_ = lean_apply_6(v_inst_1817_, v___f_1823_, lean_box(0), lean_box(0), v_it_1818_, v___x_1825_, v___f_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f(lean_object* v_00_u03b1_1829_, lean_object* v_00_u03b2_1830_, lean_object* v_m_1831_, lean_object* v_inst_1832_, lean_object* v_inst_1833_, lean_object* v_inst_1834_, lean_object* v_it_1835_, lean_object* v_f_1836_){
_start:
{
lean_object* v_toApplicative_1837_; lean_object* v_toBind_1838_; lean_object* v_toPure_1839_; lean_object* v___f_1840_; lean_object* v___f_1841_; lean_object* v___x_1842_; lean_object* v___f_1843_; lean_object* v___f_1844_; lean_object* v___x_1845_; 
v_toApplicative_1837_ = lean_ctor_get(v_inst_1832_, 0);
lean_inc_ref(v_toApplicative_1837_);
v_toBind_1838_ = lean_ctor_get(v_inst_1832_, 1);
lean_inc(v_toBind_1838_);
lean_dec_ref(v_inst_1832_);
v_toPure_1839_ = lean_ctor_get(v_toApplicative_1837_, 1);
lean_inc(v_toPure_1839_);
lean_dec_ref(v_toApplicative_1837_);
lean_inc(v_toBind_1838_);
v___f_1840_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1840_, 0, v_toBind_1838_);
lean_inc(v_toPure_1839_);
v___f_1841_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1841_, 0, v_toPure_1839_);
v___x_1842_ = lean_box(0);
lean_inc(v_toPure_1839_);
v___f_1843_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1843_, 0, v___x_1842_);
lean_closure_set(v___f_1843_, 1, v_toPure_1839_);
v___f_1844_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1844_, 0, v_toPure_1839_);
lean_closure_set(v___f_1844_, 1, v___x_1842_);
lean_closure_set(v___f_1844_, 2, v_f_1836_);
lean_closure_set(v___f_1844_, 3, v_toBind_1838_);
lean_closure_set(v___f_1844_, 4, v___f_1843_);
lean_closure_set(v___f_1844_, 5, v___f_1841_);
v___x_1845_ = lean_apply_6(v_inst_1834_, v___f_1840_, lean_box(0), lean_box(0), v_it_1835_, v___x_1842_, v___f_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f___boxed(lean_object* v_00_u03b1_1846_, lean_object* v_00_u03b2_1847_, lean_object* v_m_1848_, lean_object* v_inst_1849_, lean_object* v_inst_1850_, lean_object* v_inst_1851_, lean_object* v_it_1852_, lean_object* v_f_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Std_IterM_Partial_findM_x3f(v_00_u03b1_1846_, v_00_u03b2_1847_, v_m_1848_, v_inst_1849_, v_inst_1850_, v_inst_1851_, v_it_1852_, v_f_1853_);
lean_dec(v_inst_1850_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f___redArg(lean_object* v_inst_1855_, lean_object* v_inst_1856_, lean_object* v_it_1857_, lean_object* v_f_1858_){
_start:
{
lean_object* v_toApplicative_1859_; lean_object* v_toBind_1860_; lean_object* v_toPure_1861_; lean_object* v___f_1862_; lean_object* v___f_1863_; lean_object* v___x_1864_; lean_object* v___f_1865_; lean_object* v___f_1866_; lean_object* v___x_1867_; 
v_toApplicative_1859_ = lean_ctor_get(v_inst_1855_, 0);
lean_inc_ref(v_toApplicative_1859_);
v_toBind_1860_ = lean_ctor_get(v_inst_1855_, 1);
lean_inc(v_toBind_1860_);
lean_dec_ref(v_inst_1855_);
v_toPure_1861_ = lean_ctor_get(v_toApplicative_1859_, 1);
lean_inc(v_toPure_1861_);
lean_dec_ref(v_toApplicative_1859_);
lean_inc(v_toBind_1860_);
v___f_1862_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1862_, 0, v_toBind_1860_);
lean_inc(v_toPure_1861_);
v___f_1863_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1863_, 0, v_toPure_1861_);
v___x_1864_ = lean_box(0);
lean_inc(v_toPure_1861_);
v___f_1865_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1865_, 0, v___x_1864_);
lean_closure_set(v___f_1865_, 1, v_toPure_1861_);
v___f_1866_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1866_, 0, v_toPure_1861_);
lean_closure_set(v___f_1866_, 1, v___x_1864_);
lean_closure_set(v___f_1866_, 2, v_f_1858_);
lean_closure_set(v___f_1866_, 3, v_toBind_1860_);
lean_closure_set(v___f_1866_, 4, v___f_1865_);
lean_closure_set(v___f_1866_, 5, v___f_1863_);
v___x_1867_ = lean_apply_6(v_inst_1856_, v___f_1862_, lean_box(0), lean_box(0), v_it_1857_, v___x_1864_, v___f_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f(lean_object* v_00_u03b1_1868_, lean_object* v_00_u03b2_1869_, lean_object* v_m_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_inst_1874_, lean_object* v_it_1875_, lean_object* v_f_1876_){
_start:
{
lean_object* v_toApplicative_1877_; lean_object* v_toBind_1878_; lean_object* v_toPure_1879_; lean_object* v___f_1880_; lean_object* v___f_1881_; lean_object* v___x_1882_; lean_object* v___f_1883_; lean_object* v___f_1884_; lean_object* v___x_1885_; 
v_toApplicative_1877_ = lean_ctor_get(v_inst_1871_, 0);
lean_inc_ref(v_toApplicative_1877_);
v_toBind_1878_ = lean_ctor_get(v_inst_1871_, 1);
lean_inc(v_toBind_1878_);
lean_dec_ref(v_inst_1871_);
v_toPure_1879_ = lean_ctor_get(v_toApplicative_1877_, 1);
lean_inc(v_toPure_1879_);
lean_dec_ref(v_toApplicative_1877_);
lean_inc(v_toBind_1878_);
v___f_1880_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1880_, 0, v_toBind_1878_);
lean_inc(v_toPure_1879_);
v___f_1881_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1881_, 0, v_toPure_1879_);
v___x_1882_ = lean_box(0);
lean_inc(v_toPure_1879_);
v___f_1883_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1883_, 0, v___x_1882_);
lean_closure_set(v___f_1883_, 1, v_toPure_1879_);
v___f_1884_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1884_, 0, v_toPure_1879_);
lean_closure_set(v___f_1884_, 1, v___x_1882_);
lean_closure_set(v___f_1884_, 2, v_f_1876_);
lean_closure_set(v___f_1884_, 3, v_toBind_1878_);
lean_closure_set(v___f_1884_, 4, v___f_1883_);
lean_closure_set(v___f_1884_, 5, v___f_1881_);
v___x_1885_ = lean_apply_6(v_inst_1873_, v___f_1880_, lean_box(0), lean_box(0), v_it_1875_, v___x_1882_, v___f_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f___boxed(lean_object* v_00_u03b1_1886_, lean_object* v_00_u03b2_1887_, lean_object* v_m_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v_inst_1891_, lean_object* v_inst_1892_, lean_object* v_it_1893_, lean_object* v_f_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Std_IterM_Total_findM_x3f(v_00_u03b1_1886_, v_00_u03b2_1887_, v_m_1888_, v_inst_1889_, v_inst_1890_, v_inst_1891_, v_inst_1892_, v_it_1893_, v_f_1894_);
lean_dec(v_inst_1890_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg___lam__4(lean_object* v_toPure_1896_, lean_object* v___x_1897_, lean_object* v_f_1898_, lean_object* v_toBind_1899_, lean_object* v___f_1900_, lean_object* v___f_1901_, lean_object* v_x1_1902_, lean_object* v_x2_1903_, lean_object* v_x3_1904_){
_start:
{
lean_object* v___f_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
lean_inc(v_x1_1902_);
lean_inc(v_toPure_1896_);
v___f_1905_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_1905_, 0, v_toPure_1896_);
lean_closure_set(v___f_1905_, 1, v___x_1897_);
lean_closure_set(v___f_1905_, 2, v_x1_1902_);
v___x_1906_ = lean_apply_1(v_f_1898_, v_x1_1902_);
v___x_1907_ = lean_apply_2(v_toPure_1896_, lean_box(0), v___x_1906_);
lean_inc(v_toBind_1899_);
v___x_1908_ = lean_apply_4(v_toBind_1899_, lean_box(0), lean_box(0), v___x_1907_, v___f_1905_);
lean_inc(v_toBind_1899_);
v___x_1909_ = lean_apply_4(v_toBind_1899_, lean_box(0), lean_box(0), v___x_1908_, v___f_1900_);
v___x_1910_ = lean_apply_4(v_toBind_1899_, lean_box(0), lean_box(0), v___x_1909_, v___f_1901_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg___lam__4___boxed(lean_object* v_toPure_1911_, lean_object* v___x_1912_, lean_object* v_f_1913_, lean_object* v_toBind_1914_, lean_object* v___f_1915_, lean_object* v___f_1916_, lean_object* v_x1_1917_, lean_object* v_x2_1918_, lean_object* v_x3_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Std_IterM_find_x3f___redArg___lam__4(v_toPure_1911_, v___x_1912_, v_f_1913_, v_toBind_1914_, v___f_1915_, v___f_1916_, v_x1_1917_, v_x2_1918_, v_x3_1919_);
lean_dec(v_x3_1919_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg(lean_object* v_inst_1921_, lean_object* v_inst_1922_, lean_object* v_it_1923_, lean_object* v_f_1924_){
_start:
{
lean_object* v_toApplicative_1925_; lean_object* v_toBind_1926_; lean_object* v_toPure_1927_; lean_object* v___f_1928_; lean_object* v___f_1929_; lean_object* v___x_1930_; lean_object* v___f_1931_; lean_object* v___f_1932_; lean_object* v___x_1933_; 
v_toApplicative_1925_ = lean_ctor_get(v_inst_1921_, 0);
lean_inc_ref(v_toApplicative_1925_);
v_toBind_1926_ = lean_ctor_get(v_inst_1921_, 1);
lean_inc(v_toBind_1926_);
lean_dec_ref(v_inst_1921_);
v_toPure_1927_ = lean_ctor_get(v_toApplicative_1925_, 1);
lean_inc(v_toPure_1927_);
lean_dec_ref(v_toApplicative_1925_);
lean_inc(v_toBind_1926_);
v___f_1928_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1928_, 0, v_toBind_1926_);
lean_inc(v_toPure_1927_);
v___f_1929_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1929_, 0, v_toPure_1927_);
v___x_1930_ = lean_box(0);
lean_inc(v_toPure_1927_);
v___f_1931_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1931_, 0, v___x_1930_);
lean_closure_set(v___f_1931_, 1, v_toPure_1927_);
v___f_1932_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_1932_, 0, v_toPure_1927_);
lean_closure_set(v___f_1932_, 1, v___x_1930_);
lean_closure_set(v___f_1932_, 2, v_f_1924_);
lean_closure_set(v___f_1932_, 3, v_toBind_1926_);
lean_closure_set(v___f_1932_, 4, v___f_1931_);
lean_closure_set(v___f_1932_, 5, v___f_1929_);
v___x_1933_ = lean_apply_6(v_inst_1922_, v___f_1928_, lean_box(0), lean_box(0), v_it_1923_, v___x_1930_, v___f_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f(lean_object* v_00_u03b1_1934_, lean_object* v_00_u03b2_1935_, lean_object* v_m_1936_, lean_object* v_inst_1937_, lean_object* v_inst_1938_, lean_object* v_inst_1939_, lean_object* v_it_1940_, lean_object* v_f_1941_){
_start:
{
lean_object* v_toApplicative_1942_; lean_object* v_toBind_1943_; lean_object* v_toPure_1944_; lean_object* v___f_1945_; lean_object* v___f_1946_; lean_object* v___x_1947_; lean_object* v___f_1948_; lean_object* v___f_1949_; lean_object* v___x_1950_; 
v_toApplicative_1942_ = lean_ctor_get(v_inst_1937_, 0);
lean_inc_ref(v_toApplicative_1942_);
v_toBind_1943_ = lean_ctor_get(v_inst_1937_, 1);
lean_inc(v_toBind_1943_);
lean_dec_ref(v_inst_1937_);
v_toPure_1944_ = lean_ctor_get(v_toApplicative_1942_, 1);
lean_inc(v_toPure_1944_);
lean_dec_ref(v_toApplicative_1942_);
lean_inc(v_toBind_1943_);
v___f_1945_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1945_, 0, v_toBind_1943_);
lean_inc(v_toPure_1944_);
v___f_1946_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1946_, 0, v_toPure_1944_);
v___x_1947_ = lean_box(0);
lean_inc(v_toPure_1944_);
v___f_1948_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1948_, 0, v___x_1947_);
lean_closure_set(v___f_1948_, 1, v_toPure_1944_);
v___f_1949_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_1949_, 0, v_toPure_1944_);
lean_closure_set(v___f_1949_, 1, v___x_1947_);
lean_closure_set(v___f_1949_, 2, v_f_1941_);
lean_closure_set(v___f_1949_, 3, v_toBind_1943_);
lean_closure_set(v___f_1949_, 4, v___f_1948_);
lean_closure_set(v___f_1949_, 5, v___f_1946_);
v___x_1950_ = lean_apply_6(v_inst_1939_, v___f_1945_, lean_box(0), lean_box(0), v_it_1940_, v___x_1947_, v___f_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___boxed(lean_object* v_00_u03b1_1951_, lean_object* v_00_u03b2_1952_, lean_object* v_m_1953_, lean_object* v_inst_1954_, lean_object* v_inst_1955_, lean_object* v_inst_1956_, lean_object* v_it_1957_, lean_object* v_f_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Std_IterM_find_x3f(v_00_u03b1_1951_, v_00_u03b2_1952_, v_m_1953_, v_inst_1954_, v_inst_1955_, v_inst_1956_, v_it_1957_, v_f_1958_);
lean_dec(v_inst_1955_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f___redArg(lean_object* v_inst_1960_, lean_object* v_inst_1961_, lean_object* v_it_1962_, lean_object* v_f_1963_){
_start:
{
lean_object* v_toApplicative_1964_; lean_object* v_toBind_1965_; lean_object* v_toPure_1966_; lean_object* v___f_1967_; lean_object* v___f_1968_; lean_object* v___x_1969_; lean_object* v___f_1970_; lean_object* v___f_1971_; lean_object* v___x_1972_; 
v_toApplicative_1964_ = lean_ctor_get(v_inst_1960_, 0);
lean_inc_ref(v_toApplicative_1964_);
v_toBind_1965_ = lean_ctor_get(v_inst_1960_, 1);
lean_inc(v_toBind_1965_);
lean_dec_ref(v_inst_1960_);
v_toPure_1966_ = lean_ctor_get(v_toApplicative_1964_, 1);
lean_inc(v_toPure_1966_);
lean_dec_ref(v_toApplicative_1964_);
lean_inc(v_toBind_1965_);
v___f_1967_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1967_, 0, v_toBind_1965_);
lean_inc(v_toPure_1966_);
v___f_1968_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1968_, 0, v_toPure_1966_);
v___x_1969_ = lean_box(0);
lean_inc(v_toPure_1966_);
v___f_1970_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1970_, 0, v___x_1969_);
lean_closure_set(v___f_1970_, 1, v_toPure_1966_);
v___f_1971_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_1971_, 0, v_toPure_1966_);
lean_closure_set(v___f_1971_, 1, v___x_1969_);
lean_closure_set(v___f_1971_, 2, v_f_1963_);
lean_closure_set(v___f_1971_, 3, v_toBind_1965_);
lean_closure_set(v___f_1971_, 4, v___f_1970_);
lean_closure_set(v___f_1971_, 5, v___f_1968_);
v___x_1972_ = lean_apply_6(v_inst_1961_, v___f_1967_, lean_box(0), lean_box(0), v_it_1962_, v___x_1969_, v___f_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f(lean_object* v_00_u03b1_1973_, lean_object* v_00_u03b2_1974_, lean_object* v_m_1975_, lean_object* v_inst_1976_, lean_object* v_inst_1977_, lean_object* v_inst_1978_, lean_object* v_it_1979_, lean_object* v_f_1980_){
_start:
{
lean_object* v_toApplicative_1981_; lean_object* v_toBind_1982_; lean_object* v_toPure_1983_; lean_object* v___f_1984_; lean_object* v___f_1985_; lean_object* v___x_1986_; lean_object* v___f_1987_; lean_object* v___f_1988_; lean_object* v___x_1989_; 
v_toApplicative_1981_ = lean_ctor_get(v_inst_1976_, 0);
lean_inc_ref(v_toApplicative_1981_);
v_toBind_1982_ = lean_ctor_get(v_inst_1976_, 1);
lean_inc(v_toBind_1982_);
lean_dec_ref(v_inst_1976_);
v_toPure_1983_ = lean_ctor_get(v_toApplicative_1981_, 1);
lean_inc(v_toPure_1983_);
lean_dec_ref(v_toApplicative_1981_);
lean_inc(v_toBind_1982_);
v___f_1984_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1984_, 0, v_toBind_1982_);
lean_inc(v_toPure_1983_);
v___f_1985_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1985_, 0, v_toPure_1983_);
v___x_1986_ = lean_box(0);
lean_inc(v_toPure_1983_);
v___f_1987_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1987_, 0, v___x_1986_);
lean_closure_set(v___f_1987_, 1, v_toPure_1983_);
v___f_1988_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_1988_, 0, v_toPure_1983_);
lean_closure_set(v___f_1988_, 1, v___x_1986_);
lean_closure_set(v___f_1988_, 2, v_f_1980_);
lean_closure_set(v___f_1988_, 3, v_toBind_1982_);
lean_closure_set(v___f_1988_, 4, v___f_1987_);
lean_closure_set(v___f_1988_, 5, v___f_1985_);
v___x_1989_ = lean_apply_6(v_inst_1978_, v___f_1984_, lean_box(0), lean_box(0), v_it_1979_, v___x_1986_, v___f_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f___boxed(lean_object* v_00_u03b1_1990_, lean_object* v_00_u03b2_1991_, lean_object* v_m_1992_, lean_object* v_inst_1993_, lean_object* v_inst_1994_, lean_object* v_inst_1995_, lean_object* v_it_1996_, lean_object* v_f_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Std_IterM_Partial_find_x3f(v_00_u03b1_1990_, v_00_u03b2_1991_, v_m_1992_, v_inst_1993_, v_inst_1994_, v_inst_1995_, v_it_1996_, v_f_1997_);
lean_dec(v_inst_1994_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f___redArg(lean_object* v_inst_1999_, lean_object* v_inst_2000_, lean_object* v_it_2001_, lean_object* v_f_2002_){
_start:
{
lean_object* v_toApplicative_2003_; lean_object* v_toBind_2004_; lean_object* v_toPure_2005_; lean_object* v___f_2006_; lean_object* v___f_2007_; lean_object* v___x_2008_; lean_object* v___f_2009_; lean_object* v___f_2010_; lean_object* v___x_2011_; 
v_toApplicative_2003_ = lean_ctor_get(v_inst_1999_, 0);
lean_inc_ref(v_toApplicative_2003_);
v_toBind_2004_ = lean_ctor_get(v_inst_1999_, 1);
lean_inc(v_toBind_2004_);
lean_dec_ref(v_inst_1999_);
v_toPure_2005_ = lean_ctor_get(v_toApplicative_2003_, 1);
lean_inc(v_toPure_2005_);
lean_dec_ref(v_toApplicative_2003_);
lean_inc(v_toBind_2004_);
v___f_2006_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2006_, 0, v_toBind_2004_);
lean_inc(v_toPure_2005_);
v___f_2007_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2007_, 0, v_toPure_2005_);
v___x_2008_ = lean_box(0);
lean_inc(v_toPure_2005_);
v___f_2009_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2009_, 0, v___x_2008_);
lean_closure_set(v___f_2009_, 1, v_toPure_2005_);
v___f_2010_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_2010_, 0, v_toPure_2005_);
lean_closure_set(v___f_2010_, 1, v___x_2008_);
lean_closure_set(v___f_2010_, 2, v_f_2002_);
lean_closure_set(v___f_2010_, 3, v_toBind_2004_);
lean_closure_set(v___f_2010_, 4, v___f_2009_);
lean_closure_set(v___f_2010_, 5, v___f_2007_);
v___x_2011_ = lean_apply_6(v_inst_2000_, v___f_2006_, lean_box(0), lean_box(0), v_it_2001_, v___x_2008_, v___f_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f(lean_object* v_00_u03b1_2012_, lean_object* v_00_u03b2_2013_, lean_object* v_m_2014_, lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_it_2019_, lean_object* v_f_2020_){
_start:
{
lean_object* v_toApplicative_2021_; lean_object* v_toBind_2022_; lean_object* v_toPure_2023_; lean_object* v___f_2024_; lean_object* v___f_2025_; lean_object* v___x_2026_; lean_object* v___f_2027_; lean_object* v___f_2028_; lean_object* v___x_2029_; 
v_toApplicative_2021_ = lean_ctor_get(v_inst_2015_, 0);
lean_inc_ref(v_toApplicative_2021_);
v_toBind_2022_ = lean_ctor_get(v_inst_2015_, 1);
lean_inc(v_toBind_2022_);
lean_dec_ref(v_inst_2015_);
v_toPure_2023_ = lean_ctor_get(v_toApplicative_2021_, 1);
lean_inc(v_toPure_2023_);
lean_dec_ref(v_toApplicative_2021_);
lean_inc(v_toBind_2022_);
v___f_2024_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2024_, 0, v_toBind_2022_);
lean_inc(v_toPure_2023_);
v___f_2025_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2025_, 0, v_toPure_2023_);
v___x_2026_ = lean_box(0);
lean_inc(v_toPure_2023_);
v___f_2027_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2027_, 0, v___x_2026_);
lean_closure_set(v___f_2027_, 1, v_toPure_2023_);
v___f_2028_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_2028_, 0, v_toPure_2023_);
lean_closure_set(v___f_2028_, 1, v___x_2026_);
lean_closure_set(v___f_2028_, 2, v_f_2020_);
lean_closure_set(v___f_2028_, 3, v_toBind_2022_);
lean_closure_set(v___f_2028_, 4, v___f_2027_);
lean_closure_set(v___f_2028_, 5, v___f_2025_);
v___x_2029_ = lean_apply_6(v_inst_2017_, v___f_2024_, lean_box(0), lean_box(0), v_it_2019_, v___x_2026_, v___f_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f___boxed(lean_object* v_00_u03b1_2030_, lean_object* v_00_u03b2_2031_, lean_object* v_m_2032_, lean_object* v_inst_2033_, lean_object* v_inst_2034_, lean_object* v_inst_2035_, lean_object* v_inst_2036_, lean_object* v_it_2037_, lean_object* v_f_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Std_IterM_Total_find_x3f(v_00_u03b1_2030_, v_00_u03b2_2031_, v_m_2032_, v_inst_2033_, v_inst_2034_, v_inst_2035_, v_inst_2036_, v_it_2037_, v_f_2038_);
lean_dec(v_inst_2034_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg___lam__0(lean_object* v_toBind_2040_, lean_object* v_x_2041_, lean_object* v_x_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = lean_apply_4(v_toBind_2040_, lean_box(0), lean_box(0), v___y_2044_, v___y_2043_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg___lam__1(lean_object* v_toPure_2046_, lean_object* v_b_2047_, lean_object* v_x_2048_, lean_object* v_x_2049_){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2050_, 0, v_b_2047_);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
v___x_2052_ = lean_apply_2(v_toPure_2046_, lean_box(0), v___x_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg___lam__1___boxed(lean_object* v_toPure_2053_, lean_object* v_b_2054_, lean_object* v_x_2055_, lean_object* v_x_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Std_IterM_first_x3f___redArg___lam__1(v_toPure_2053_, v_b_2054_, v_x_2055_, v_x_2056_);
lean_dec(v_x_2056_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg(lean_object* v_inst_2058_, lean_object* v_inst_2059_, lean_object* v_it_2060_){
_start:
{
lean_object* v_toApplicative_2061_; lean_object* v_toBind_2062_; lean_object* v_toPure_2063_; lean_object* v___f_2064_; lean_object* v___f_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v_toApplicative_2061_ = lean_ctor_get(v_inst_2058_, 0);
lean_inc_ref(v_toApplicative_2061_);
v_toBind_2062_ = lean_ctor_get(v_inst_2058_, 1);
lean_inc(v_toBind_2062_);
lean_dec_ref(v_inst_2058_);
v_toPure_2063_ = lean_ctor_get(v_toApplicative_2061_, 1);
lean_inc(v_toPure_2063_);
lean_dec_ref(v_toApplicative_2061_);
v___f_2064_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2064_, 0, v_toBind_2062_);
v___f_2065_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2065_, 0, v_toPure_2063_);
v___x_2066_ = lean_box(0);
v___x_2067_ = lean_apply_6(v_inst_2059_, v___f_2064_, lean_box(0), lean_box(0), v_it_2060_, v___x_2066_, v___f_2065_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f(lean_object* v_00_u03b1_2068_, lean_object* v_00_u03b2_2069_, lean_object* v_m_2070_, lean_object* v_inst_2071_, lean_object* v_inst_2072_, lean_object* v_inst_2073_, lean_object* v_it_2074_){
_start:
{
lean_object* v_toApplicative_2075_; lean_object* v_toBind_2076_; lean_object* v_toPure_2077_; lean_object* v___f_2078_; lean_object* v___f_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v_toApplicative_2075_ = lean_ctor_get(v_inst_2071_, 0);
lean_inc_ref(v_toApplicative_2075_);
v_toBind_2076_ = lean_ctor_get(v_inst_2071_, 1);
lean_inc(v_toBind_2076_);
lean_dec_ref(v_inst_2071_);
v_toPure_2077_ = lean_ctor_get(v_toApplicative_2075_, 1);
lean_inc(v_toPure_2077_);
lean_dec_ref(v_toApplicative_2075_);
v___f_2078_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2078_, 0, v_toBind_2076_);
v___f_2079_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2079_, 0, v_toPure_2077_);
v___x_2080_ = lean_box(0);
v___x_2081_ = lean_apply_6(v_inst_2073_, v___f_2078_, lean_box(0), lean_box(0), v_it_2074_, v___x_2080_, v___f_2079_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___boxed(lean_object* v_00_u03b1_2082_, lean_object* v_00_u03b2_2083_, lean_object* v_m_2084_, lean_object* v_inst_2085_, lean_object* v_inst_2086_, lean_object* v_inst_2087_, lean_object* v_it_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Std_IterM_first_x3f(v_00_u03b1_2082_, v_00_u03b2_2083_, v_m_2084_, v_inst_2085_, v_inst_2086_, v_inst_2087_, v_it_2088_);
lean_dec(v_inst_2086_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_first_x3f___redArg(lean_object* v_inst_2090_, lean_object* v_inst_2091_, lean_object* v_it_2092_){
_start:
{
lean_object* v_toApplicative_2093_; lean_object* v_toBind_2094_; lean_object* v_toPure_2095_; lean_object* v___f_2096_; lean_object* v___f_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v_toApplicative_2093_ = lean_ctor_get(v_inst_2090_, 0);
lean_inc_ref(v_toApplicative_2093_);
v_toBind_2094_ = lean_ctor_get(v_inst_2090_, 1);
lean_inc(v_toBind_2094_);
lean_dec_ref(v_inst_2090_);
v_toPure_2095_ = lean_ctor_get(v_toApplicative_2093_, 1);
lean_inc(v_toPure_2095_);
lean_dec_ref(v_toApplicative_2093_);
v___f_2096_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2096_, 0, v_toBind_2094_);
v___f_2097_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2097_, 0, v_toPure_2095_);
v___x_2098_ = lean_box(0);
v___x_2099_ = lean_apply_6(v_inst_2091_, v___f_2096_, lean_box(0), lean_box(0), v_it_2092_, v___x_2098_, v___f_2097_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_first_x3f(lean_object* v_00_u03b1_2100_, lean_object* v_00_u03b2_2101_, lean_object* v_m_2102_, lean_object* v_inst_2103_, lean_object* v_inst_2104_, lean_object* v_inst_2105_, lean_object* v_inst_2106_, lean_object* v_it_2107_){
_start:
{
lean_object* v_toApplicative_2108_; lean_object* v_toBind_2109_; lean_object* v_toPure_2110_; lean_object* v___f_2111_; lean_object* v___f_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v_toApplicative_2108_ = lean_ctor_get(v_inst_2103_, 0);
lean_inc_ref(v_toApplicative_2108_);
v_toBind_2109_ = lean_ctor_get(v_inst_2103_, 1);
lean_inc(v_toBind_2109_);
lean_dec_ref(v_inst_2103_);
v_toPure_2110_ = lean_ctor_get(v_toApplicative_2108_, 1);
lean_inc(v_toPure_2110_);
lean_dec_ref(v_toApplicative_2108_);
v___f_2111_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2111_, 0, v_toBind_2109_);
v___f_2112_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2112_, 0, v_toPure_2110_);
v___x_2113_ = lean_box(0);
v___x_2114_ = lean_apply_6(v_inst_2105_, v___f_2111_, lean_box(0), lean_box(0), v_it_2107_, v___x_2113_, v___f_2112_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_first_x3f___boxed(lean_object* v_00_u03b1_2115_, lean_object* v_00_u03b2_2116_, lean_object* v_m_2117_, lean_object* v_inst_2118_, lean_object* v_inst_2119_, lean_object* v_inst_2120_, lean_object* v_inst_2121_, lean_object* v_it_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Std_IterM_Total_first_x3f(v_00_u03b1_2115_, v_00_u03b2_2116_, v_m_2117_, v_inst_2118_, v_inst_2119_, v_inst_2120_, v_inst_2121_, v_it_2122_);
lean_dec(v_inst_2119_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___redArg___lam__1(lean_object* v_toPure_2127_, lean_object* v_x_2128_, lean_object* v_x_2129_, uint8_t v_x_2130_){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = ((lean_object*)(l_Std_IterM_isEmpty___redArg___lam__1___closed__0));
v___x_2132_ = lean_apply_2(v_toPure_2127_, lean_box(0), v___x_2131_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___redArg___lam__1___boxed(lean_object* v_toPure_2133_, lean_object* v_x_2134_, lean_object* v_x_2135_, lean_object* v_x_2136_){
_start:
{
uint8_t v_x_79__boxed_2137_; lean_object* v_res_2138_; 
v_x_79__boxed_2137_ = lean_unbox(v_x_2136_);
v_res_2138_ = l_Std_IterM_isEmpty___redArg___lam__1(v_toPure_2133_, v_x_2134_, v_x_2135_, v_x_79__boxed_2137_);
lean_dec(v_x_2134_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___redArg(lean_object* v_inst_2139_, lean_object* v_inst_2140_, lean_object* v_it_2141_){
_start:
{
lean_object* v_toApplicative_2142_; lean_object* v_toBind_2143_; lean_object* v_toPure_2144_; lean_object* v___f_2145_; lean_object* v___f_2146_; uint8_t v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v_toApplicative_2142_ = lean_ctor_get(v_inst_2139_, 0);
lean_inc_ref(v_toApplicative_2142_);
v_toBind_2143_ = lean_ctor_get(v_inst_2139_, 1);
lean_inc(v_toBind_2143_);
lean_dec_ref(v_inst_2139_);
v_toPure_2144_ = lean_ctor_get(v_toApplicative_2142_, 1);
lean_inc(v_toPure_2144_);
lean_dec_ref(v_toApplicative_2142_);
v___f_2145_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2145_, 0, v_toBind_2143_);
v___f_2146_ = lean_alloc_closure((void*)(l_Std_IterM_isEmpty___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2146_, 0, v_toPure_2144_);
v___x_2147_ = 1;
v___x_2148_ = lean_box(v___x_2147_);
v___x_2149_ = lean_apply_6(v_inst_2140_, v___f_2145_, lean_box(0), lean_box(0), v_it_2141_, v___x_2148_, v___f_2146_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty(lean_object* v_00_u03b1_2150_, lean_object* v_00_u03b2_2151_, lean_object* v_m_2152_, lean_object* v_inst_2153_, lean_object* v_inst_2154_, lean_object* v_inst_2155_, lean_object* v_it_2156_){
_start:
{
lean_object* v_toApplicative_2157_; lean_object* v_toBind_2158_; lean_object* v_toPure_2159_; lean_object* v___f_2160_; lean_object* v___f_2161_; uint8_t v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v_toApplicative_2157_ = lean_ctor_get(v_inst_2153_, 0);
lean_inc_ref(v_toApplicative_2157_);
v_toBind_2158_ = lean_ctor_get(v_inst_2153_, 1);
lean_inc(v_toBind_2158_);
lean_dec_ref(v_inst_2153_);
v_toPure_2159_ = lean_ctor_get(v_toApplicative_2157_, 1);
lean_inc(v_toPure_2159_);
lean_dec_ref(v_toApplicative_2157_);
v___f_2160_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2160_, 0, v_toBind_2158_);
v___f_2161_ = lean_alloc_closure((void*)(l_Std_IterM_isEmpty___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2161_, 0, v_toPure_2159_);
v___x_2162_ = 1;
v___x_2163_ = lean_box(v___x_2162_);
v___x_2164_ = lean_apply_6(v_inst_2155_, v___f_2160_, lean_box(0), lean_box(0), v_it_2156_, v___x_2163_, v___f_2161_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___boxed(lean_object* v_00_u03b1_2165_, lean_object* v_00_u03b2_2166_, lean_object* v_m_2167_, lean_object* v_inst_2168_, lean_object* v_inst_2169_, lean_object* v_inst_2170_, lean_object* v_it_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Std_IterM_isEmpty(v_00_u03b1_2165_, v_00_u03b2_2166_, v_m_2167_, v_inst_2168_, v_inst_2169_, v_inst_2170_, v_it_2171_);
lean_dec(v_inst_2169_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_isEmpty___redArg(lean_object* v_inst_2173_, lean_object* v_inst_2174_, lean_object* v_it_2175_){
_start:
{
lean_object* v_toApplicative_2176_; lean_object* v_toBind_2177_; lean_object* v_toPure_2178_; lean_object* v___f_2179_; lean_object* v___f_2180_; uint8_t v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v_toApplicative_2176_ = lean_ctor_get(v_inst_2173_, 0);
lean_inc_ref(v_toApplicative_2176_);
v_toBind_2177_ = lean_ctor_get(v_inst_2173_, 1);
lean_inc(v_toBind_2177_);
lean_dec_ref(v_inst_2173_);
v_toPure_2178_ = lean_ctor_get(v_toApplicative_2176_, 1);
lean_inc(v_toPure_2178_);
lean_dec_ref(v_toApplicative_2176_);
v___f_2179_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2179_, 0, v_toBind_2177_);
v___f_2180_ = lean_alloc_closure((void*)(l_Std_IterM_isEmpty___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2180_, 0, v_toPure_2178_);
v___x_2181_ = 1;
v___x_2182_ = lean_box(v___x_2181_);
v___x_2183_ = lean_apply_6(v_inst_2174_, v___f_2179_, lean_box(0), lean_box(0), v_it_2175_, v___x_2182_, v___f_2180_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_isEmpty(lean_object* v_00_u03b1_2184_, lean_object* v_00_u03b2_2185_, lean_object* v_m_2186_, lean_object* v_inst_2187_, lean_object* v_inst_2188_, lean_object* v_inst_2189_, lean_object* v_inst_2190_, lean_object* v_it_2191_){
_start:
{
lean_object* v_toApplicative_2192_; lean_object* v_toBind_2193_; lean_object* v_toPure_2194_; lean_object* v___f_2195_; lean_object* v___f_2196_; uint8_t v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v_toApplicative_2192_ = lean_ctor_get(v_inst_2187_, 0);
lean_inc_ref(v_toApplicative_2192_);
v_toBind_2193_ = lean_ctor_get(v_inst_2187_, 1);
lean_inc(v_toBind_2193_);
lean_dec_ref(v_inst_2187_);
v_toPure_2194_ = lean_ctor_get(v_toApplicative_2192_, 1);
lean_inc(v_toPure_2194_);
lean_dec_ref(v_toApplicative_2192_);
v___f_2195_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2195_, 0, v_toBind_2193_);
v___f_2196_ = lean_alloc_closure((void*)(l_Std_IterM_isEmpty___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2196_, 0, v_toPure_2194_);
v___x_2197_ = 1;
v___x_2198_ = lean_box(v___x_2197_);
v___x_2199_ = lean_apply_6(v_inst_2189_, v___f_2195_, lean_box(0), lean_box(0), v_it_2191_, v___x_2198_, v___f_2196_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_isEmpty___boxed(lean_object* v_00_u03b1_2200_, lean_object* v_00_u03b2_2201_, lean_object* v_m_2202_, lean_object* v_inst_2203_, lean_object* v_inst_2204_, lean_object* v_inst_2205_, lean_object* v_inst_2206_, lean_object* v_it_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Std_IterM_Total_isEmpty(v_00_u03b1_2200_, v_00_u03b2_2201_, v_m_2202_, v_inst_2203_, v_inst_2204_, v_inst_2205_, v_inst_2206_, v_it_2207_);
lean_dec(v_inst_2204_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg___lam__1(lean_object* v_toPure_2209_, lean_object* v_____do__lift_2210_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = lean_apply_2(v_toPure_2209_, lean_box(0), v_____do__lift_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg___lam__0(lean_object* v_toPure_2212_, lean_object* v_toBind_2213_, lean_object* v___f_2214_, lean_object* v_x1_2215_, lean_object* v_x2_2216_, lean_object* v_x3_2217_){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2218_ = lean_unsigned_to_nat(1u);
v___x_2219_ = lean_nat_add(v_x3_2217_, v___x_2218_);
v___x_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
v___x_2221_ = lean_apply_2(v_toPure_2212_, lean_box(0), v___x_2220_);
v___x_2222_ = lean_apply_4(v_toBind_2213_, lean_box(0), lean_box(0), v___x_2221_, v___f_2214_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg___lam__0___boxed(lean_object* v_toPure_2223_, lean_object* v_toBind_2224_, lean_object* v___f_2225_, lean_object* v_x1_2226_, lean_object* v_x2_2227_, lean_object* v_x3_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Std_IterM_length___redArg___lam__0(v_toPure_2223_, v_toBind_2224_, v___f_2225_, v_x1_2226_, v_x2_2227_, v_x3_2228_);
lean_dec(v_x3_2228_);
lean_dec(v_x1_2226_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg(lean_object* v_inst_2230_, lean_object* v_inst_2231_, lean_object* v_it_2232_){
_start:
{
lean_object* v_toApplicative_2233_; lean_object* v_toBind_2234_; lean_object* v_toPure_2235_; lean_object* v___x_2236_; lean_object* v___f_2237_; lean_object* v___f_2238_; lean_object* v___f_2239_; lean_object* v___x_2240_; 
v_toApplicative_2233_ = lean_ctor_get(v_inst_2231_, 0);
lean_inc_ref(v_toApplicative_2233_);
v_toBind_2234_ = lean_ctor_get(v_inst_2231_, 1);
lean_inc(v_toBind_2234_);
lean_dec_ref(v_inst_2231_);
v_toPure_2235_ = lean_ctor_get(v_toApplicative_2233_, 1);
lean_inc(v_toPure_2235_);
lean_dec_ref(v_toApplicative_2233_);
v___x_2236_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2234_);
v___f_2237_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2237_, 0, v_toBind_2234_);
lean_inc(v_toPure_2235_);
v___f_2238_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2238_, 0, v_toPure_2235_);
v___f_2239_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2239_, 0, v_toPure_2235_);
lean_closure_set(v___f_2239_, 1, v_toBind_2234_);
lean_closure_set(v___f_2239_, 2, v___f_2238_);
v___x_2240_ = lean_apply_6(v_inst_2230_, v___f_2237_, lean_box(0), lean_box(0), v_it_2232_, v___x_2236_, v___f_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length(lean_object* v_00_u03b1_2241_, lean_object* v_m_2242_, lean_object* v_00_u03b2_2243_, lean_object* v_inst_2244_, lean_object* v_inst_2245_, lean_object* v_inst_2246_, lean_object* v_it_2247_){
_start:
{
lean_object* v_toApplicative_2248_; lean_object* v_toBind_2249_; lean_object* v_toPure_2250_; lean_object* v___x_2251_; lean_object* v___f_2252_; lean_object* v___f_2253_; lean_object* v___f_2254_; lean_object* v___x_2255_; 
v_toApplicative_2248_ = lean_ctor_get(v_inst_2246_, 0);
lean_inc_ref(v_toApplicative_2248_);
v_toBind_2249_ = lean_ctor_get(v_inst_2246_, 1);
lean_inc(v_toBind_2249_);
lean_dec_ref(v_inst_2246_);
v_toPure_2250_ = lean_ctor_get(v_toApplicative_2248_, 1);
lean_inc(v_toPure_2250_);
lean_dec_ref(v_toApplicative_2248_);
v___x_2251_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2249_);
v___f_2252_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2252_, 0, v_toBind_2249_);
lean_inc(v_toPure_2250_);
v___f_2253_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2253_, 0, v_toPure_2250_);
v___f_2254_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2254_, 0, v_toPure_2250_);
lean_closure_set(v___f_2254_, 1, v_toBind_2249_);
lean_closure_set(v___f_2254_, 2, v___f_2253_);
v___x_2255_ = lean_apply_6(v_inst_2245_, v___f_2252_, lean_box(0), lean_box(0), v_it_2247_, v___x_2251_, v___f_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___boxed(lean_object* v_00_u03b1_2256_, lean_object* v_m_2257_, lean_object* v_00_u03b2_2258_, lean_object* v_inst_2259_, lean_object* v_inst_2260_, lean_object* v_inst_2261_, lean_object* v_it_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Std_IterM_length(v_00_u03b1_2256_, v_m_2257_, v_00_u03b2_2258_, v_inst_2259_, v_inst_2260_, v_inst_2261_, v_it_2262_);
lean_dec(v_inst_2259_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_count___redArg(lean_object* v_inst_2264_, lean_object* v_inst_2265_, lean_object* v_it_2266_){
_start:
{
lean_object* v_toApplicative_2267_; lean_object* v_toBind_2268_; lean_object* v_toPure_2269_; lean_object* v___x_2270_; lean_object* v___f_2271_; lean_object* v___f_2272_; lean_object* v___f_2273_; lean_object* v___x_2274_; 
v_toApplicative_2267_ = lean_ctor_get(v_inst_2265_, 0);
lean_inc_ref(v_toApplicative_2267_);
v_toBind_2268_ = lean_ctor_get(v_inst_2265_, 1);
lean_inc(v_toBind_2268_);
lean_dec_ref(v_inst_2265_);
v_toPure_2269_ = lean_ctor_get(v_toApplicative_2267_, 1);
lean_inc(v_toPure_2269_);
lean_dec_ref(v_toApplicative_2267_);
v___x_2270_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2268_);
v___f_2271_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2271_, 0, v_toBind_2268_);
lean_inc(v_toPure_2269_);
v___f_2272_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2272_, 0, v_toPure_2269_);
v___f_2273_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2273_, 0, v_toPure_2269_);
lean_closure_set(v___f_2273_, 1, v_toBind_2268_);
lean_closure_set(v___f_2273_, 2, v___f_2272_);
v___x_2274_ = lean_apply_6(v_inst_2264_, v___f_2271_, lean_box(0), lean_box(0), v_it_2266_, v___x_2270_, v___f_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_count(lean_object* v_00_u03b1_2275_, lean_object* v_m_2276_, lean_object* v_00_u03b2_2277_, lean_object* v_inst_2278_, lean_object* v_inst_2279_, lean_object* v_inst_2280_, lean_object* v_it_2281_){
_start:
{
lean_object* v_toApplicative_2282_; lean_object* v_toBind_2283_; lean_object* v_toPure_2284_; lean_object* v___x_2285_; lean_object* v___f_2286_; lean_object* v___f_2287_; lean_object* v___f_2288_; lean_object* v___x_2289_; 
v_toApplicative_2282_ = lean_ctor_get(v_inst_2280_, 0);
lean_inc_ref(v_toApplicative_2282_);
v_toBind_2283_ = lean_ctor_get(v_inst_2280_, 1);
lean_inc(v_toBind_2283_);
lean_dec_ref(v_inst_2280_);
v_toPure_2284_ = lean_ctor_get(v_toApplicative_2282_, 1);
lean_inc(v_toPure_2284_);
lean_dec_ref(v_toApplicative_2282_);
v___x_2285_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2283_);
v___f_2286_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2286_, 0, v_toBind_2283_);
lean_inc(v_toPure_2284_);
v___f_2287_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2287_, 0, v_toPure_2284_);
v___f_2288_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2288_, 0, v_toPure_2284_);
lean_closure_set(v___f_2288_, 1, v_toBind_2283_);
lean_closure_set(v___f_2288_, 2, v___f_2287_);
v___x_2289_ = lean_apply_6(v_inst_2279_, v___f_2286_, lean_box(0), lean_box(0), v_it_2281_, v___x_2285_, v___f_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_count___boxed(lean_object* v_00_u03b1_2290_, lean_object* v_m_2291_, lean_object* v_00_u03b2_2292_, lean_object* v_inst_2293_, lean_object* v_inst_2294_, lean_object* v_inst_2295_, lean_object* v_it_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Std_IterM_count(v_00_u03b1_2290_, v_m_2291_, v_00_u03b2_2292_, v_inst_2293_, v_inst_2294_, v_inst_2295_, v_it_2296_);
lean_dec(v_inst_2293_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_size___redArg(lean_object* v_inst_2298_, lean_object* v_inst_2299_, lean_object* v_it_2300_){
_start:
{
lean_object* v_toApplicative_2301_; lean_object* v_toBind_2302_; lean_object* v_toPure_2303_; lean_object* v___x_2304_; lean_object* v___f_2305_; lean_object* v___f_2306_; lean_object* v___f_2307_; lean_object* v___x_2308_; 
v_toApplicative_2301_ = lean_ctor_get(v_inst_2299_, 0);
lean_inc_ref(v_toApplicative_2301_);
v_toBind_2302_ = lean_ctor_get(v_inst_2299_, 1);
lean_inc(v_toBind_2302_);
lean_dec_ref(v_inst_2299_);
v_toPure_2303_ = lean_ctor_get(v_toApplicative_2301_, 1);
lean_inc(v_toPure_2303_);
lean_dec_ref(v_toApplicative_2301_);
v___x_2304_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2302_);
v___f_2305_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2305_, 0, v_toBind_2302_);
lean_inc(v_toPure_2303_);
v___f_2306_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2306_, 0, v_toPure_2303_);
v___f_2307_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2307_, 0, v_toPure_2303_);
lean_closure_set(v___f_2307_, 1, v_toBind_2302_);
lean_closure_set(v___f_2307_, 2, v___f_2306_);
v___x_2308_ = lean_apply_6(v_inst_2298_, v___f_2305_, lean_box(0), lean_box(0), v_it_2300_, v___x_2304_, v___f_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_size(lean_object* v_00_u03b1_2309_, lean_object* v_m_2310_, lean_object* v_00_u03b2_2311_, lean_object* v_inst_2312_, lean_object* v_inst_2313_, lean_object* v_inst_2314_, lean_object* v_it_2315_){
_start:
{
lean_object* v_toApplicative_2316_; lean_object* v_toBind_2317_; lean_object* v_toPure_2318_; lean_object* v___x_2319_; lean_object* v___f_2320_; lean_object* v___f_2321_; lean_object* v___f_2322_; lean_object* v___x_2323_; 
v_toApplicative_2316_ = lean_ctor_get(v_inst_2314_, 0);
lean_inc_ref(v_toApplicative_2316_);
v_toBind_2317_ = lean_ctor_get(v_inst_2314_, 1);
lean_inc(v_toBind_2317_);
lean_dec_ref(v_inst_2314_);
v_toPure_2318_ = lean_ctor_get(v_toApplicative_2316_, 1);
lean_inc(v_toPure_2318_);
lean_dec_ref(v_toApplicative_2316_);
v___x_2319_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2317_);
v___f_2320_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2320_, 0, v_toBind_2317_);
lean_inc(v_toPure_2318_);
v___f_2321_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2321_, 0, v_toPure_2318_);
v___f_2322_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2322_, 0, v_toPure_2318_);
lean_closure_set(v___f_2322_, 1, v_toBind_2317_);
lean_closure_set(v___f_2322_, 2, v___f_2321_);
v___x_2323_ = lean_apply_6(v_inst_2313_, v___f_2320_, lean_box(0), lean_box(0), v_it_2315_, v___x_2319_, v___f_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_size___boxed(lean_object* v_00_u03b1_2324_, lean_object* v_m_2325_, lean_object* v_00_u03b2_2326_, lean_object* v_inst_2327_, lean_object* v_inst_2328_, lean_object* v_inst_2329_, lean_object* v_it_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Std_IterM_size(v_00_u03b1_2324_, v_m_2325_, v_00_u03b2_2326_, v_inst_2327_, v_inst_2328_, v_inst_2329_, v_it_2330_);
lean_dec(v_inst_2327_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count___redArg(lean_object* v_inst_2332_, lean_object* v_inst_2333_, lean_object* v_it_2334_){
_start:
{
lean_object* v_toApplicative_2335_; lean_object* v_toBind_2336_; lean_object* v_toPure_2337_; lean_object* v___x_2338_; lean_object* v___f_2339_; lean_object* v___f_2340_; lean_object* v___f_2341_; lean_object* v___x_2342_; 
v_toApplicative_2335_ = lean_ctor_get(v_inst_2333_, 0);
lean_inc_ref(v_toApplicative_2335_);
v_toBind_2336_ = lean_ctor_get(v_inst_2333_, 1);
lean_inc(v_toBind_2336_);
lean_dec_ref(v_inst_2333_);
v_toPure_2337_ = lean_ctor_get(v_toApplicative_2335_, 1);
lean_inc(v_toPure_2337_);
lean_dec_ref(v_toApplicative_2335_);
v___x_2338_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2336_);
v___f_2339_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2339_, 0, v_toBind_2336_);
lean_inc(v_toPure_2337_);
v___f_2340_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2340_, 0, v_toPure_2337_);
v___f_2341_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2341_, 0, v_toPure_2337_);
lean_closure_set(v___f_2341_, 1, v_toBind_2336_);
lean_closure_set(v___f_2341_, 2, v___f_2340_);
v___x_2342_ = lean_apply_6(v_inst_2332_, v___f_2339_, lean_box(0), lean_box(0), v_it_2334_, v___x_2338_, v___f_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count(lean_object* v_00_u03b1_2343_, lean_object* v_m_2344_, lean_object* v_00_u03b2_2345_, lean_object* v_inst_2346_, lean_object* v_inst_2347_, lean_object* v_inst_2348_, lean_object* v_it_2349_){
_start:
{
lean_object* v_toApplicative_2350_; lean_object* v_toBind_2351_; lean_object* v_toPure_2352_; lean_object* v___x_2353_; lean_object* v___f_2354_; lean_object* v___f_2355_; lean_object* v___f_2356_; lean_object* v___x_2357_; 
v_toApplicative_2350_ = lean_ctor_get(v_inst_2348_, 0);
lean_inc_ref(v_toApplicative_2350_);
v_toBind_2351_ = lean_ctor_get(v_inst_2348_, 1);
lean_inc(v_toBind_2351_);
lean_dec_ref(v_inst_2348_);
v_toPure_2352_ = lean_ctor_get(v_toApplicative_2350_, 1);
lean_inc(v_toPure_2352_);
lean_dec_ref(v_toApplicative_2350_);
v___x_2353_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2351_);
v___f_2354_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2354_, 0, v_toBind_2351_);
lean_inc(v_toPure_2352_);
v___f_2355_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2355_, 0, v_toPure_2352_);
v___f_2356_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2356_, 0, v_toPure_2352_);
lean_closure_set(v___f_2356_, 1, v_toBind_2351_);
lean_closure_set(v___f_2356_, 2, v___f_2355_);
v___x_2357_ = lean_apply_6(v_inst_2347_, v___f_2354_, lean_box(0), lean_box(0), v_it_2349_, v___x_2353_, v___f_2356_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count___boxed(lean_object* v_00_u03b1_2358_, lean_object* v_m_2359_, lean_object* v_00_u03b2_2360_, lean_object* v_inst_2361_, lean_object* v_inst_2362_, lean_object* v_inst_2363_, lean_object* v_it_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Std_IterM_Partial_count(v_00_u03b1_2358_, v_m_2359_, v_00_u03b2_2360_, v_inst_2361_, v_inst_2362_, v_inst_2363_, v_it_2364_);
lean_dec(v_inst_2361_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size___redArg(lean_object* v_inst_2366_, lean_object* v_inst_2367_, lean_object* v_it_2368_){
_start:
{
lean_object* v_toApplicative_2369_; lean_object* v_toBind_2370_; lean_object* v_toPure_2371_; lean_object* v___x_2372_; lean_object* v___f_2373_; lean_object* v___f_2374_; lean_object* v___f_2375_; lean_object* v___x_2376_; 
v_toApplicative_2369_ = lean_ctor_get(v_inst_2367_, 0);
lean_inc_ref(v_toApplicative_2369_);
v_toBind_2370_ = lean_ctor_get(v_inst_2367_, 1);
lean_inc(v_toBind_2370_);
lean_dec_ref(v_inst_2367_);
v_toPure_2371_ = lean_ctor_get(v_toApplicative_2369_, 1);
lean_inc(v_toPure_2371_);
lean_dec_ref(v_toApplicative_2369_);
v___x_2372_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2370_);
v___f_2373_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2373_, 0, v_toBind_2370_);
lean_inc(v_toPure_2371_);
v___f_2374_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2374_, 0, v_toPure_2371_);
v___f_2375_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2375_, 0, v_toPure_2371_);
lean_closure_set(v___f_2375_, 1, v_toBind_2370_);
lean_closure_set(v___f_2375_, 2, v___f_2374_);
v___x_2376_ = lean_apply_6(v_inst_2366_, v___f_2373_, lean_box(0), lean_box(0), v_it_2368_, v___x_2372_, v___f_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size(lean_object* v_00_u03b1_2377_, lean_object* v_m_2378_, lean_object* v_00_u03b2_2379_, lean_object* v_inst_2380_, lean_object* v_inst_2381_, lean_object* v_inst_2382_, lean_object* v_it_2383_){
_start:
{
lean_object* v_toApplicative_2384_; lean_object* v_toBind_2385_; lean_object* v_toPure_2386_; lean_object* v___x_2387_; lean_object* v___f_2388_; lean_object* v___f_2389_; lean_object* v___f_2390_; lean_object* v___x_2391_; 
v_toApplicative_2384_ = lean_ctor_get(v_inst_2382_, 0);
lean_inc_ref(v_toApplicative_2384_);
v_toBind_2385_ = lean_ctor_get(v_inst_2382_, 1);
lean_inc(v_toBind_2385_);
lean_dec_ref(v_inst_2382_);
v_toPure_2386_ = lean_ctor_get(v_toApplicative_2384_, 1);
lean_inc(v_toPure_2386_);
lean_dec_ref(v_toApplicative_2384_);
v___x_2387_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_2385_);
v___f_2388_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2388_, 0, v_toBind_2385_);
lean_inc(v_toPure_2386_);
v___f_2389_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2389_, 0, v_toPure_2386_);
v___f_2390_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2390_, 0, v_toPure_2386_);
lean_closure_set(v___f_2390_, 1, v_toBind_2385_);
lean_closure_set(v___f_2390_, 2, v___f_2389_);
v___x_2391_ = lean_apply_6(v_inst_2381_, v___f_2388_, lean_box(0), lean_box(0), v_it_2383_, v___x_2387_, v___f_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size___boxed(lean_object* v_00_u03b1_2392_, lean_object* v_m_2393_, lean_object* v_00_u03b2_2394_, lean_object* v_inst_2395_, lean_object* v_inst_2396_, lean_object* v_inst_2397_, lean_object* v_it_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Std_IterM_Partial_size(v_00_u03b1_2392_, v_m_2393_, v_00_u03b2_2394_, v_inst_2395_, v_inst_2396_, v_inst_2397_, v_it_2398_);
lean_dec(v_inst_2395_);
return v_res_2399_;
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
