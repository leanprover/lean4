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
LEAN_EXPORT lean_object* l_Std_IteratorLoop_WithWF_instWellFoundedRelation___redArg();
LEAN_EXPORT lean_object* l_Std_IteratorLoop_WithWF_instWellFoundedRelation___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_IteratorLoop_WithWF_instWellFoundedRelation___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_WithWF_instWellFoundedRelation___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_IteratorLoop_WithWF_instWellFoundedRelation___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_WithWF_instWellFoundedRelation(lean_object* v_00_u03b1_5_, lean_object* v_m_6_, lean_object* v_00_u03b2_7_, lean_object* v_inst_8_, lean_object* v_00_u03b3_9_, lean_object* v_PlausibleForInStep_10_, lean_object* v_hwf_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_box(0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_WithWF_instWellFoundedRelation___boxed(lean_object* v_00_u03b1_13_, lean_object* v_m_14_, lean_object* v_00_u03b2_15_, lean_object* v_inst_16_, lean_object* v_00_u03b3_17_, lean_object* v_PlausibleForInStep_18_, lean_object* v_hwf_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_IteratorLoop_WithWF_instWellFoundedRelation(v_00_u03b1_13_, v_m_14_, v_00_u03b2_15_, v_inst_16_, v_00_u03b3_17_, v_PlausibleForInStep_18_, v_hwf_19_);
lean_dec(v_inst_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0(lean_object* v_toPure_21_, lean_object* v_recur_22_, lean_object* v_it_23_, lean_object* v_____do__lift_24_){
_start:
{
if (lean_obj_tag(v_____do__lift_24_) == 0)
{
lean_object* v_a_25_; lean_object* v___x_26_; 
lean_dec(v_it_23_);
lean_dec(v_recur_22_);
v_a_25_ = lean_ctor_get(v_____do__lift_24_, 0);
lean_inc(v_a_25_);
lean_dec_ref_known(v_____do__lift_24_, 1);
v___x_26_ = lean_apply_2(v_toPure_21_, lean_box(0), v_a_25_);
return v___x_26_;
}
else
{
lean_object* v_a_27_; lean_object* v___x_28_; 
lean_dec(v_toPure_21_);
v_a_27_ = lean_ctor_get(v_____do__lift_24_, 0);
lean_inc(v_a_27_);
lean_dec_ref_known(v_____do__lift_24_, 1);
v___x_28_ = lean_apply_4(v_recur_22_, v_it_23_, v_a_27_, lean_box(0), lean_box(0));
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__1(lean_object* v_toPure_29_, lean_object* v_recur_30_, lean_object* v_f_31_, lean_object* v_acc_32_, lean_object* v_toBind_33_, lean_object* v_s_34_){
_start:
{
switch(lean_obj_tag(v_s_34_))
{
case 0:
{
lean_object* v_it_35_; lean_object* v_out_36_; lean_object* v___f_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_it_35_ = lean_ctor_get(v_s_34_, 0);
lean_inc(v_it_35_);
v_out_36_ = lean_ctor_get(v_s_34_, 1);
lean_inc(v_out_36_);
lean_dec_ref_known(v_s_34_, 2);
v___f_37_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_37_, 0, v_toPure_29_);
lean_closure_set(v___f_37_, 1, v_recur_30_);
lean_closure_set(v___f_37_, 2, v_it_35_);
v___x_38_ = lean_apply_3(v_f_31_, v_out_36_, lean_box(0), v_acc_32_);
v___x_39_ = lean_apply_4(v_toBind_33_, lean_box(0), lean_box(0), v___x_38_, v___f_37_);
return v___x_39_;
}
case 1:
{
lean_object* v_it_40_; lean_object* v___x_41_; 
lean_dec(v_toBind_33_);
lean_dec(v_f_31_);
lean_dec(v_toPure_29_);
v_it_40_ = lean_ctor_get(v_s_34_, 0);
lean_inc(v_it_40_);
lean_dec_ref_known(v_s_34_, 1);
v___x_41_ = lean_apply_4(v_recur_30_, v_it_40_, v_acc_32_, lean_box(0), lean_box(0));
return v___x_41_;
}
default: 
{
lean_object* v___x_42_; 
lean_dec(v_toBind_33_);
lean_dec(v_f_31_);
lean_dec(v_recur_30_);
v___x_42_ = lean_apply_2(v_toPure_29_, lean_box(0), v_acc_32_);
return v___x_42_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2(lean_object* v_toPure_43_, lean_object* v_f_44_, lean_object* v_toBind_45_, lean_object* v_inst_46_, lean_object* v_lift_47_, lean_object* v_it_48_, lean_object* v_acc_49_, lean_object* v_hP_50_, lean_object* v_recur_51_){
_start:
{
lean_object* v___f_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___f_52_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__1), 6, 5);
lean_closure_set(v___f_52_, 0, v_toPure_43_);
lean_closure_set(v___f_52_, 1, v_recur_51_);
lean_closure_set(v___f_52_, 2, v_f_44_);
lean_closure_set(v___f_52_, 3, v_acc_49_);
lean_closure_set(v___f_52_, 4, v_toBind_45_);
v___x_53_ = lean_apply_1(v_inst_46_, v_it_48_);
v___x_54_ = lean_apply_4(v_lift_47_, lean_box(0), lean_box(0), v___f_52_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg(lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_lift_57_, lean_object* v_it_58_, lean_object* v_init_59_, lean_object* v_f_60_){
_start:
{
lean_object* v_toApplicative_61_; lean_object* v_toBind_62_; lean_object* v_toPure_63_; lean_object* v___f_64_; lean_object* v___x_65_; 
v_toApplicative_61_ = lean_ctor_get(v_inst_56_, 0);
lean_inc_ref(v_toApplicative_61_);
v_toBind_62_ = lean_ctor_get(v_inst_56_, 1);
lean_inc(v_toBind_62_);
lean_dec_ref(v_inst_56_);
v_toPure_63_ = lean_ctor_get(v_toApplicative_61_, 1);
lean_inc(v_toPure_63_);
lean_dec_ref(v_toApplicative_61_);
v___f_64_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2), 9, 5);
lean_closure_set(v___f_64_, 0, v_toPure_63_);
lean_closure_set(v___f_64_, 1, v_f_60_);
lean_closure_set(v___f_64_, 2, v_toBind_62_);
lean_closure_set(v___f_64_, 3, v_inst_55_);
lean_closure_set(v___f_64_, 4, v_lift_57_);
v___x_65_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_64_, v_it_58_, v_init_59_, lean_box(0));
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27(lean_object* v_m_66_, lean_object* v_00_u03b1_67_, lean_object* v_00_u03b2_68_, lean_object* v_inst_69_, lean_object* v_n_70_, lean_object* v_inst_71_, lean_object* v_lift_72_, lean_object* v_00_u03b3_73_, lean_object* v_PlausibleForInStep_74_, lean_object* v_it_75_, lean_object* v_init_76_, lean_object* v_P_77_, lean_object* v_hP_78_, lean_object* v_f_79_){
_start:
{
lean_object* v_toApplicative_80_; lean_object* v_toBind_81_; lean_object* v_toPure_82_; lean_object* v___f_83_; lean_object* v___x_84_; 
v_toApplicative_80_ = lean_ctor_get(v_inst_71_, 0);
lean_inc_ref(v_toApplicative_80_);
v_toBind_81_ = lean_ctor_get(v_inst_71_, 1);
lean_inc(v_toBind_81_);
lean_dec_ref(v_inst_71_);
v_toPure_82_ = lean_ctor_get(v_toApplicative_80_, 1);
lean_inc(v_toPure_82_);
lean_dec_ref(v_toApplicative_80_);
v___f_83_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2), 9, 5);
lean_closure_set(v___f_83_, 0, v_toPure_82_);
lean_closure_set(v___f_83_, 1, v_f_79_);
lean_closure_set(v___f_83_, 2, v_toBind_81_);
lean_closure_set(v___f_83_, 3, v_inst_69_);
lean_closure_set(v___f_83_, 4, v_lift_72_);
v___x_84_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_83_, v_it_75_, v_init_76_, lean_box(0));
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__1(lean_object* v_toPure_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_lift_88_, lean_object* v_f_89_, lean_object* v_init_90_, lean_object* v_toBind_91_, lean_object* v_s_92_){
_start:
{
switch(lean_obj_tag(v_s_92_))
{
case 0:
{
lean_object* v_it_93_; lean_object* v_out_94_; lean_object* v___f_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v_it_93_ = lean_ctor_get(v_s_92_, 0);
lean_inc(v_it_93_);
v_out_94_ = lean_ctor_get(v_s_92_, 1);
lean_inc(v_out_94_);
lean_dec_ref_known(v_s_92_, 2);
lean_inc(v_f_89_);
v___f_95_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__0), 7, 6);
lean_closure_set(v___f_95_, 0, v_toPure_85_);
lean_closure_set(v___f_95_, 1, v_inst_86_);
lean_closure_set(v___f_95_, 2, v_inst_87_);
lean_closure_set(v___f_95_, 3, v_lift_88_);
lean_closure_set(v___f_95_, 4, v_it_93_);
lean_closure_set(v___f_95_, 5, v_f_89_);
v___x_96_ = lean_apply_3(v_f_89_, v_out_94_, lean_box(0), v_init_90_);
v___x_97_ = lean_apply_4(v_toBind_91_, lean_box(0), lean_box(0), v___x_96_, v___f_95_);
return v___x_97_;
}
case 1:
{
lean_object* v_it_98_; lean_object* v___x_99_; 
lean_dec(v_toBind_91_);
lean_dec(v_toPure_85_);
v_it_98_ = lean_ctor_get(v_s_92_, 0);
lean_inc(v_it_98_);
lean_dec_ref_known(v_s_92_, 1);
v___x_99_ = l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(v_inst_86_, v_inst_87_, v_lift_88_, v_it_98_, v_init_90_, v_f_89_);
return v___x_99_;
}
default: 
{
lean_object* v___x_100_; 
lean_dec(v_toBind_91_);
lean_dec(v_f_89_);
lean_dec(v_lift_88_);
lean_dec_ref(v_inst_87_);
lean_dec(v_inst_86_);
v___x_100_ = lean_apply_2(v_toPure_85_, lean_box(0), v_init_90_);
return v___x_100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_lift_103_, lean_object* v_it_104_, lean_object* v_init_105_, lean_object* v_f_106_){
_start:
{
lean_object* v_toApplicative_107_; lean_object* v_toBind_108_; lean_object* v_toPure_109_; lean_object* v___f_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_toApplicative_107_ = lean_ctor_get(v_inst_102_, 0);
v_toBind_108_ = lean_ctor_get(v_inst_102_, 1);
lean_inc(v_toBind_108_);
v_toPure_109_ = lean_ctor_get(v_toApplicative_107_, 1);
lean_inc(v_toPure_109_);
lean_inc(v_lift_103_);
lean_inc(v_inst_101_);
v___f_110_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__1), 8, 7);
lean_closure_set(v___f_110_, 0, v_toPure_109_);
lean_closure_set(v___f_110_, 1, v_inst_101_);
lean_closure_set(v___f_110_, 2, v_inst_102_);
lean_closure_set(v___f_110_, 3, v_lift_103_);
lean_closure_set(v___f_110_, 4, v_f_106_);
lean_closure_set(v___f_110_, 5, v_init_105_);
lean_closure_set(v___f_110_, 6, v_toBind_108_);
v___x_111_ = lean_apply_1(v_inst_101_, v_it_104_);
v___x_112_ = lean_apply_4(v_lift_103_, lean_box(0), lean_box(0), v___f_110_, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__0(lean_object* v_toPure_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_lift_116_, lean_object* v_it_117_, lean_object* v_f_118_, lean_object* v_____do__lift_119_){
_start:
{
if (lean_obj_tag(v_____do__lift_119_) == 0)
{
lean_object* v_a_120_; lean_object* v___x_121_; 
lean_dec(v_f_118_);
lean_dec(v_it_117_);
lean_dec(v_lift_116_);
lean_dec_ref(v_inst_115_);
lean_dec(v_inst_114_);
v_a_120_ = lean_ctor_get(v_____do__lift_119_, 0);
lean_inc(v_a_120_);
lean_dec_ref_known(v_____do__lift_119_, 1);
v___x_121_ = lean_apply_2(v_toPure_113_, lean_box(0), v_a_120_);
return v___x_121_;
}
else
{
lean_object* v_a_122_; lean_object* v___x_123_; 
lean_dec(v_toPure_113_);
v_a_122_ = lean_ctor_get(v_____do__lift_119_, 0);
lean_inc(v_a_122_);
lean_dec_ref_known(v_____do__lift_119_, 1);
v___x_123_ = l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(v_inst_114_, v_inst_115_, v_lift_116_, v_it_117_, v_a_122_, v_f_118_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf(lean_object* v_m_124_, lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_inst_127_, lean_object* v_n_128_, lean_object* v_inst_129_, lean_object* v_lift_130_, lean_object* v_00_u03b3_131_, lean_object* v_PlausibleForInStep_132_, lean_object* v_wf_133_, lean_object* v_it_134_, lean_object* v_init_135_, lean_object* v_P_136_, lean_object* v_hP_137_, lean_object* v_f_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(v_inst_127_, v_inst_129_, v_lift_130_, v_it_134_, v_init_135_, v_f_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(lean_object* v_x_140_, lean_object* v_h__1_141_, lean_object* v_h__2_142_, lean_object* v_h__3_143_){
_start:
{
switch(lean_obj_tag(v_x_140_))
{
case 0:
{
lean_object* v_it_144_; lean_object* v_out_145_; lean_object* v___x_146_; 
lean_dec(v_h__3_143_);
lean_dec(v_h__2_142_);
v_it_144_ = lean_ctor_get(v_x_140_, 0);
lean_inc(v_it_144_);
v_out_145_ = lean_ctor_get(v_x_140_, 1);
lean_inc(v_out_145_);
lean_dec_ref_known(v_x_140_, 2);
v___x_146_ = lean_apply_3(v_h__1_141_, v_it_144_, v_out_145_, lean_box(0));
return v___x_146_;
}
case 1:
{
lean_object* v_it_147_; lean_object* v___x_148_; 
lean_dec(v_h__3_143_);
lean_dec(v_h__1_141_);
v_it_147_ = lean_ctor_get(v_x_140_, 0);
lean_inc(v_it_147_);
lean_dec_ref_known(v_x_140_, 1);
v___x_148_ = lean_apply_2(v_h__2_142_, v_it_147_, lean_box(0));
return v___x_148_;
}
default: 
{
lean_object* v___x_149_; 
lean_dec(v_h__2_142_);
lean_dec(v_h__1_141_);
v___x_149_ = lean_apply_1(v_h__3_143_, lean_box(0));
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(lean_object* v_m_150_, lean_object* v_00_u03b1_151_, lean_object* v_00_u03b2_152_, lean_object* v_inst_153_, lean_object* v_it_154_, lean_object* v_motive_155_, lean_object* v_x_156_, lean_object* v_h__1_157_, lean_object* v_h__2_158_, lean_object* v_h__3_159_){
_start:
{
switch(lean_obj_tag(v_x_156_))
{
case 0:
{
lean_object* v_it_160_; lean_object* v_out_161_; lean_object* v___x_162_; 
lean_dec(v_h__3_159_);
lean_dec(v_h__2_158_);
v_it_160_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_it_160_);
v_out_161_ = lean_ctor_get(v_x_156_, 1);
lean_inc(v_out_161_);
lean_dec_ref_known(v_x_156_, 2);
v___x_162_ = lean_apply_3(v_h__1_157_, v_it_160_, v_out_161_, lean_box(0));
return v___x_162_;
}
case 1:
{
lean_object* v_it_163_; lean_object* v___x_164_; 
lean_dec(v_h__3_159_);
lean_dec(v_h__1_157_);
v_it_163_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_it_163_);
lean_dec_ref_known(v_x_156_, 1);
v___x_164_ = lean_apply_2(v_h__2_158_, v_it_163_, lean_box(0));
return v___x_164_;
}
default: 
{
lean_object* v___x_165_; 
lean_dec(v_h__2_158_);
lean_dec(v_h__1_157_);
v___x_165_ = lean_apply_1(v_h__3_159_, lean_box(0));
return v___x_165_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(lean_object* v_m_166_, lean_object* v_00_u03b1_167_, lean_object* v_00_u03b2_168_, lean_object* v_inst_169_, lean_object* v_it_170_, lean_object* v_motive_171_, lean_object* v_x_172_, lean_object* v_h__1_173_, lean_object* v_h__2_174_, lean_object* v_h__3_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(v_m_166_, v_00_u03b1_167_, v_00_u03b2_168_, v_inst_169_, v_it_170_, v_motive_171_, v_x_172_, v_h__1_173_, v_h__2_174_, v_h__3_175_);
lean_dec(v_it_170_);
lean_dec(v_inst_169_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(lean_object* v_____do__lift_177_, lean_object* v_h__1_178_, lean_object* v_h__2_179_){
_start:
{
if (lean_obj_tag(v_____do__lift_177_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_181_; 
lean_dec(v_h__1_178_);
v_a_180_ = lean_ctor_get(v_____do__lift_177_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v_____do__lift_177_, 1);
v___x_181_ = lean_apply_2(v_h__2_179_, v_a_180_, lean_box(0));
return v___x_181_;
}
else
{
lean_object* v_a_182_; lean_object* v___x_183_; 
lean_dec(v_h__2_179_);
v_a_182_ = lean_ctor_get(v_____do__lift_177_, 0);
lean_inc(v_a_182_);
lean_dec_ref_known(v_____do__lift_177_, 1);
v___x_183_ = lean_apply_2(v_h__1_178_, v_a_182_, lean_box(0));
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(lean_object* v_00_u03b2_184_, lean_object* v_00_u03b3_185_, lean_object* v_PlausibleForInStep_186_, lean_object* v_acc_187_, lean_object* v_out_188_, lean_object* v_motive_189_, lean_object* v_____do__lift_190_, lean_object* v_h__1_191_, lean_object* v_h__2_192_){
_start:
{
if (lean_obj_tag(v_____do__lift_190_) == 0)
{
lean_object* v_a_193_; lean_object* v___x_194_; 
lean_dec(v_h__1_191_);
v_a_193_ = lean_ctor_get(v_____do__lift_190_, 0);
lean_inc(v_a_193_);
lean_dec_ref_known(v_____do__lift_190_, 1);
v___x_194_ = lean_apply_2(v_h__2_192_, v_a_193_, lean_box(0));
return v___x_194_;
}
else
{
lean_object* v_a_195_; lean_object* v___x_196_; 
lean_dec(v_h__2_192_);
v_a_195_ = lean_ctor_get(v_____do__lift_190_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v_____do__lift_190_, 1);
v___x_196_ = lean_apply_2(v_h__1_191_, v_a_195_, lean_box(0));
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(lean_object* v_00_u03b2_197_, lean_object* v_00_u03b3_198_, lean_object* v_PlausibleForInStep_199_, lean_object* v_acc_200_, lean_object* v_out_201_, lean_object* v_motive_202_, lean_object* v_____do__lift_203_, lean_object* v_h__1_204_, lean_object* v_h__2_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(v_00_u03b2_197_, v_00_u03b3_198_, v_PlausibleForInStep_199_, v_acc_200_, v_out_201_, v_motive_202_, v_____do__lift_203_, v_h__1_204_, v_h__2_205_);
lean_dec(v_out_201_);
lean_dec(v_acc_200_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__1(lean_object* v_toPure_207_, lean_object* v_recur_208_, lean_object* v___y_209_, lean_object* v_acc_210_, lean_object* v_toBind_211_, lean_object* v_s_212_){
_start:
{
switch(lean_obj_tag(v_s_212_))
{
case 0:
{
lean_object* v_it_213_; lean_object* v_out_214_; lean_object* v___f_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_it_213_ = lean_ctor_get(v_s_212_, 0);
lean_inc(v_it_213_);
v_out_214_ = lean_ctor_get(v_s_212_, 1);
lean_inc(v_out_214_);
lean_dec_ref_known(v_s_212_, 2);
v___f_215_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_215_, 0, v_toPure_207_);
lean_closure_set(v___f_215_, 1, v_recur_208_);
lean_closure_set(v___f_215_, 2, v_it_213_);
v___x_216_ = lean_apply_3(v___y_209_, v_out_214_, lean_box(0), v_acc_210_);
v___x_217_ = lean_apply_4(v_toBind_211_, lean_box(0), lean_box(0), v___x_216_, v___f_215_);
return v___x_217_;
}
case 1:
{
lean_object* v_it_218_; lean_object* v___x_219_; 
lean_dec(v_toBind_211_);
lean_dec(v___y_209_);
lean_dec(v_toPure_207_);
v_it_218_ = lean_ctor_get(v_s_212_, 0);
lean_inc(v_it_218_);
lean_dec_ref_known(v_s_212_, 1);
v___x_219_ = lean_apply_4(v_recur_208_, v_it_218_, v_acc_210_, lean_box(0), lean_box(0));
return v___x_219_;
}
default: 
{
lean_object* v___x_220_; 
lean_dec(v_toBind_211_);
lean_dec(v___y_209_);
lean_dec(v_recur_208_);
v___x_220_ = lean_apply_2(v_toPure_207_, lean_box(0), v_acc_210_);
return v___x_220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__0(lean_object* v_toPure_221_, lean_object* v___y_222_, lean_object* v_toBind_223_, lean_object* v_inst_224_, lean_object* v_lift_225_, lean_object* v_it_226_, lean_object* v_acc_227_, lean_object* v_hP_228_, lean_object* v_recur_229_){
_start:
{
lean_object* v___f_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___f_230_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__1), 6, 5);
lean_closure_set(v___f_230_, 0, v_toPure_221_);
lean_closure_set(v___f_230_, 1, v_recur_229_);
lean_closure_set(v___f_230_, 2, v___y_222_);
lean_closure_set(v___f_230_, 3, v_acc_227_);
lean_closure_set(v___f_230_, 4, v_toBind_223_);
v___x_231_ = lean_apply_1(v_inst_224_, v_it_226_);
v___x_232_ = lean_apply_4(v_lift_225_, lean_box(0), lean_box(0), v___f_230_, v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__2(lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_lift_235_, lean_object* v_00_u03b3_236_, lean_object* v_Pl_237_, lean_object* v_it_238_, lean_object* v_init_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_toApplicative_241_; lean_object* v_toBind_242_; lean_object* v_toPure_243_; lean_object* v___f_244_; lean_object* v___x_245_; 
v_toApplicative_241_ = lean_ctor_get(v_inst_233_, 0);
lean_inc_ref(v_toApplicative_241_);
v_toBind_242_ = lean_ctor_get(v_inst_233_, 1);
lean_inc(v_toBind_242_);
lean_dec_ref(v_inst_233_);
v_toPure_243_ = lean_ctor_get(v_toApplicative_241_, 1);
lean_inc(v_toPure_243_);
lean_dec_ref(v_toApplicative_241_);
v___f_244_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__0), 9, 5);
lean_closure_set(v___f_244_, 0, v_toPure_243_);
lean_closure_set(v___f_244_, 1, v___y_240_);
lean_closure_set(v___f_244_, 2, v_toBind_242_);
lean_closure_set(v___f_244_, 3, v_inst_234_);
lean_closure_set(v___f_244_, 4, v_lift_235_);
v___x_245_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_244_, v_it_238_, v_init_239_, lean_box(0));
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg(lean_object* v_inst_246_, lean_object* v_inst_247_){
_start:
{
lean_object* v___f_248_; 
v___f_248_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__2), 8, 2);
lean_closure_set(v___f_248_, 0, v_inst_246_);
lean_closure_set(v___f_248_, 1, v_inst_247_);
return v___f_248_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation(lean_object* v_00_u03b2_249_, lean_object* v_00_u03b1_250_, lean_object* v_m_251_, lean_object* v_n_252_, lean_object* v_inst_253_, lean_object* v_inst_254_){
_start:
{
lean_object* v___f_255_; 
v___f_255_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__2), 8, 2);
lean_closure_set(v___f_255_, 0, v_inst_253_);
lean_closure_set(v___f_255_, 1, v_inst_254_);
return v___f_255_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0(lean_object* v_toPure_256_, lean_object* v_____do__lift_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lean_apply_2(v_toPure_256_, lean_box(0), v_____do__lift_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1(lean_object* v_f_259_, lean_object* v_toBind_260_, lean_object* v___f_261_, lean_object* v_x1_262_, lean_object* v_x2_263_, lean_object* v_x3_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_apply_3(v_f_259_, v_x1_262_, lean_box(0), v_x3_264_);
v___x_266_ = lean_apply_4(v_toBind_260_, lean_box(0), lean_box(0), v___x_265_, v___f_261_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2(lean_object* v_toBind_267_, lean_object* v___f_268_, lean_object* v_inst_269_, lean_object* v_lift_270_, lean_object* v_00_u03b3_271_, lean_object* v_it_272_, lean_object* v_init_273_, lean_object* v_f_274_){
_start:
{
lean_object* v___f_275_; lean_object* v___x_276_; 
v___f_275_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1), 6, 3);
lean_closure_set(v___f_275_, 0, v_f_274_);
lean_closure_set(v___f_275_, 1, v_toBind_267_);
lean_closure_set(v___f_275_, 2, v___f_268_);
v___x_276_ = lean_apply_6(v_inst_269_, v_lift_270_, lean_box(0), lean_box(0), v_it_272_, v_init_273_, v___f_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg(lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_lift_279_){
_start:
{
lean_object* v_toApplicative_280_; lean_object* v_toBind_281_; lean_object* v_toPure_282_; lean_object* v___f_283_; lean_object* v___f_284_; 
v_toApplicative_280_ = lean_ctor_get(v_inst_278_, 0);
lean_inc_ref(v_toApplicative_280_);
v_toBind_281_ = lean_ctor_get(v_inst_278_, 1);
lean_inc(v_toBind_281_);
lean_dec_ref(v_inst_278_);
v_toPure_282_ = lean_ctor_get(v_toApplicative_280_, 1);
lean_inc(v_toPure_282_);
lean_dec_ref(v_toApplicative_280_);
v___f_283_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_283_, 0, v_toPure_282_);
v___f_284_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2), 8, 4);
lean_closure_set(v___f_284_, 0, v_toBind_281_);
lean_closure_set(v___f_284_, 1, v___f_283_);
lean_closure_set(v___f_284_, 2, v_inst_277_);
lean_closure_set(v___f_284_, 3, v_lift_279_);
return v___f_284_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27(lean_object* v_m_285_, lean_object* v_n_286_, lean_object* v_00_u03b1_287_, lean_object* v_00_u03b2_288_, lean_object* v_inst_289_, lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_lift_292_){
_start:
{
lean_object* v_toApplicative_293_; lean_object* v_toBind_294_; lean_object* v_toPure_295_; lean_object* v___f_296_; lean_object* v___f_297_; 
v_toApplicative_293_ = lean_ctor_get(v_inst_291_, 0);
lean_inc_ref(v_toApplicative_293_);
v_toBind_294_ = lean_ctor_get(v_inst_291_, 1);
lean_inc(v_toBind_294_);
lean_dec_ref(v_inst_291_);
v_toPure_295_ = lean_ctor_get(v_toApplicative_293_, 1);
lean_inc(v_toPure_295_);
lean_dec_ref(v_toApplicative_293_);
v___f_296_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_296_, 0, v_toPure_295_);
v___f_297_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2), 8, 4);
lean_closure_set(v___f_297_, 0, v_toBind_294_);
lean_closure_set(v___f_297_, 1, v___f_296_);
lean_closure_set(v___f_297_, 2, v_inst_290_);
lean_closure_set(v___f_297_, 3, v_lift_292_);
return v___f_297_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___boxed(lean_object* v_m_298_, lean_object* v_n_299_, lean_object* v_00_u03b1_300_, lean_object* v_00_u03b2_301_, lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_inst_304_, lean_object* v_lift_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Std_IteratorLoop_finiteForIn_x27(v_m_298_, v_n_299_, v_00_u03b1_300_, v_00_u03b2_301_, v_inst_302_, v_inst_303_, v_inst_304_, v_lift_305_);
lean_dec(v_inst_302_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg___lam__0(lean_object* v_inst_307_, lean_object* v_toBind_308_, lean_object* v_x_309_, lean_object* v_x_310_, lean_object* v_f_311_, lean_object* v_x_312_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_apply_2(v_inst_307_, lean_box(0), v_x_312_);
v___x_314_ = lean_apply_4(v_toBind_308_, lean_box(0), lean_box(0), v___x_313_, v_f_311_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg___lam__3(lean_object* v_toBind_315_, lean_object* v___f_316_, lean_object* v_inst_317_, lean_object* v___f_318_, lean_object* v_00_u03b3_319_, lean_object* v_it_320_, lean_object* v_init_321_, lean_object* v_f_322_){
_start:
{
lean_object* v___f_323_; lean_object* v___x_324_; 
v___f_323_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1), 6, 3);
lean_closure_set(v___f_323_, 0, v_f_322_);
lean_closure_set(v___f_323_, 1, v_toBind_315_);
lean_closure_set(v___f_323_, 2, v___f_316_);
v___x_324_ = lean_apply_6(v_inst_317_, v___f_318_, lean_box(0), lean_box(0), v_it_320_, v_init_321_, v___f_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg(lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_inst_327_){
_start:
{
lean_object* v_toApplicative_328_; lean_object* v_toBind_329_; lean_object* v_toPure_330_; lean_object* v___f_331_; lean_object* v___f_332_; lean_object* v___f_333_; 
v_toApplicative_328_ = lean_ctor_get(v_inst_326_, 0);
lean_inc_ref(v_toApplicative_328_);
v_toBind_329_ = lean_ctor_get(v_inst_326_, 1);
lean_inc_n(v_toBind_329_, 2);
lean_dec_ref(v_inst_326_);
v_toPure_330_ = lean_ctor_get(v_toApplicative_328_, 1);
lean_inc(v_toPure_330_);
lean_dec_ref(v_toApplicative_328_);
v___f_331_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_331_, 0, v_inst_327_);
lean_closure_set(v___f_331_, 1, v_toBind_329_);
v___f_332_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_332_, 0, v_toPure_330_);
v___f_333_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_333_, 0, v_toBind_329_);
lean_closure_set(v___f_333_, 1, v___f_332_);
lean_closure_set(v___f_333_, 2, v_inst_325_);
lean_closure_set(v___f_333_, 3, v___f_331_);
return v___f_333_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27(lean_object* v_m_334_, lean_object* v_n_335_, lean_object* v_00_u03b1_336_, lean_object* v_00_u03b2_337_, lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_inst_341_){
_start:
{
lean_object* v_toApplicative_342_; lean_object* v_toBind_343_; lean_object* v_toPure_344_; lean_object* v___f_345_; lean_object* v___f_346_; lean_object* v___f_347_; 
v_toApplicative_342_ = lean_ctor_get(v_inst_340_, 0);
lean_inc_ref(v_toApplicative_342_);
v_toBind_343_ = lean_ctor_get(v_inst_340_, 1);
lean_inc_n(v_toBind_343_, 2);
lean_dec_ref(v_inst_340_);
v_toPure_344_ = lean_ctor_get(v_toApplicative_342_, 1);
lean_inc(v_toPure_344_);
lean_dec_ref(v_toApplicative_342_);
v___f_345_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_345_, 0, v_inst_341_);
lean_closure_set(v___f_345_, 1, v_toBind_343_);
v___f_346_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_346_, 0, v_toPure_344_);
v___f_347_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_347_, 0, v_toBind_343_);
lean_closure_set(v___f_347_, 1, v___f_346_);
lean_closure_set(v___f_347_, 2, v_inst_339_);
lean_closure_set(v___f_347_, 3, v___f_345_);
return v___f_347_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___boxed(lean_object* v_m_348_, lean_object* v_n_349_, lean_object* v_00_u03b1_350_, lean_object* v_00_u03b2_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_inst_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Std_IterM_instForIn_x27(v_m_348_, v_n_349_, v_00_u03b1_350_, v_00_u03b2_351_, v_inst_352_, v_inst_353_, v_inst_354_, v_inst_355_);
lean_dec(v_inst_352_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop___redArg(lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_inst_359_){
_start:
{
lean_object* v_toApplicative_360_; lean_object* v_toBind_361_; lean_object* v_toPure_362_; lean_object* v___f_363_; lean_object* v___f_364_; lean_object* v___f_365_; lean_object* v___f_366_; 
v_toApplicative_360_ = lean_ctor_get(v_inst_359_, 0);
lean_inc_ref(v_toApplicative_360_);
v_toBind_361_ = lean_ctor_get(v_inst_359_, 1);
lean_inc_n(v_toBind_361_, 2);
lean_dec_ref(v_inst_359_);
v_toPure_362_ = lean_ctor_get(v_toApplicative_360_, 1);
lean_inc(v_toPure_362_);
lean_dec_ref(v_toApplicative_360_);
v___f_363_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_363_, 0, v_inst_358_);
lean_closure_set(v___f_363_, 1, v_toBind_361_);
v___f_364_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_364_, 0, v_toPure_362_);
v___f_365_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_365_, 0, v_toBind_361_);
lean_closure_set(v___f_365_, 1, v___f_364_);
lean_closure_set(v___f_365_, 2, v_inst_357_);
lean_closure_set(v___f_365_, 3, v___f_363_);
v___f_366_ = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(v___f_366_, 0, v___f_365_);
return v___f_366_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop(lean_object* v_m_367_, lean_object* v_n_368_, lean_object* v_00_u03b1_369_, lean_object* v_00_u03b2_370_, lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_inst_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Std_IterM_instForInOfIteratorLoop___redArg(v_inst_372_, v_inst_373_, v_inst_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop___boxed(lean_object* v_m_376_, lean_object* v_n_377_, lean_object* v_00_u03b1_378_, lean_object* v_00_u03b2_379_, lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_inst_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Std_IterM_instForInOfIteratorLoop(v_m_376_, v_n_377_, v_00_u03b1_378_, v_00_u03b2_379_, v_inst_380_, v_inst_381_, v_inst_382_, v_inst_383_);
lean_dec(v_inst_380_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___redArg___lam__3(lean_object* v_toBind_385_, lean_object* v___f_386_, lean_object* v_inst_387_, lean_object* v___f_388_, lean_object* v_00_u03b2_389_, lean_object* v_it_390_, lean_object* v_init_391_, lean_object* v_f_392_){
_start:
{
lean_object* v___f_393_; lean_object* v___x_394_; 
v___f_393_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1), 6, 3);
lean_closure_set(v___f_393_, 0, v_f_392_);
lean_closure_set(v___f_393_, 1, v_toBind_385_);
lean_closure_set(v___f_393_, 2, v___f_386_);
v___x_394_ = lean_apply_6(v_inst_387_, v___f_388_, lean_box(0), lean_box(0), v_it_390_, v_init_391_, v___f_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___redArg(lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_inst_397_){
_start:
{
lean_object* v_toApplicative_398_; lean_object* v_toBind_399_; lean_object* v_toPure_400_; lean_object* v___f_401_; lean_object* v___f_402_; lean_object* v___f_403_; 
v_toApplicative_398_ = lean_ctor_get(v_inst_397_, 0);
lean_inc_ref(v_toApplicative_398_);
v_toBind_399_ = lean_ctor_get(v_inst_397_, 1);
lean_inc_n(v_toBind_399_, 2);
lean_dec_ref(v_inst_397_);
v_toPure_400_ = lean_ctor_get(v_toApplicative_398_, 1);
lean_inc(v_toPure_400_);
lean_dec_ref(v_toApplicative_398_);
v___f_401_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_401_, 0, v_inst_396_);
lean_closure_set(v___f_401_, 1, v_toBind_399_);
v___f_402_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_402_, 0, v_toPure_400_);
v___f_403_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_403_, 0, v_toBind_399_);
lean_closure_set(v___f_403_, 1, v___f_402_);
lean_closure_set(v___f_403_, 2, v_inst_395_);
lean_closure_set(v___f_403_, 3, v___f_401_);
return v___f_403_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27(lean_object* v_m_404_, lean_object* v_n_405_, lean_object* v_00_u03b1_406_, lean_object* v_00_u03b2_407_, lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_inst_411_){
_start:
{
lean_object* v_toApplicative_412_; lean_object* v_toBind_413_; lean_object* v_toPure_414_; lean_object* v___f_415_; lean_object* v___f_416_; lean_object* v___f_417_; 
v_toApplicative_412_ = lean_ctor_get(v_inst_411_, 0);
lean_inc_ref(v_toApplicative_412_);
v_toBind_413_ = lean_ctor_get(v_inst_411_, 1);
lean_inc_n(v_toBind_413_, 2);
lean_dec_ref(v_inst_411_);
v_toPure_414_ = lean_ctor_get(v_toApplicative_412_, 1);
lean_inc(v_toPure_414_);
lean_dec_ref(v_toApplicative_412_);
v___f_415_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_415_, 0, v_inst_410_);
lean_closure_set(v___f_415_, 1, v_toBind_413_);
v___f_416_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_416_, 0, v_toPure_414_);
v___f_417_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_417_, 0, v_toBind_413_);
lean_closure_set(v___f_417_, 1, v___f_416_);
lean_closure_set(v___f_417_, 2, v_inst_409_);
lean_closure_set(v___f_417_, 3, v___f_415_);
return v___f_417_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___boxed(lean_object* v_m_418_, lean_object* v_n_419_, lean_object* v_00_u03b1_420_, lean_object* v_00_u03b2_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_inst_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_IterM_Partial_instForIn_x27(v_m_418_, v_n_419_, v_00_u03b1_420_, v_00_u03b2_421_, v_inst_422_, v_inst_423_, v_inst_424_, v_inst_425_);
lean_dec(v_inst_422_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27___redArg(lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_inst_429_){
_start:
{
lean_object* v_toApplicative_430_; lean_object* v_toBind_431_; lean_object* v_toPure_432_; lean_object* v___f_433_; lean_object* v___f_434_; lean_object* v___f_435_; 
v_toApplicative_430_ = lean_ctor_get(v_inst_429_, 0);
lean_inc_ref(v_toApplicative_430_);
v_toBind_431_ = lean_ctor_get(v_inst_429_, 1);
lean_inc_n(v_toBind_431_, 2);
lean_dec_ref(v_inst_429_);
v_toPure_432_ = lean_ctor_get(v_toApplicative_430_, 1);
lean_inc(v_toPure_432_);
lean_dec_ref(v_toApplicative_430_);
v___f_433_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_433_, 0, v_inst_428_);
lean_closure_set(v___f_433_, 1, v_toBind_431_);
v___f_434_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_434_, 0, v_toPure_432_);
v___f_435_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_435_, 0, v_toBind_431_);
lean_closure_set(v___f_435_, 1, v___f_434_);
lean_closure_set(v___f_435_, 2, v_inst_427_);
lean_closure_set(v___f_435_, 3, v___f_433_);
return v___f_435_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27(lean_object* v_m_436_, lean_object* v_n_437_, lean_object* v_00_u03b1_438_, lean_object* v_00_u03b2_439_, lean_object* v_inst_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_inst_444_){
_start:
{
lean_object* v_toApplicative_445_; lean_object* v_toBind_446_; lean_object* v_toPure_447_; lean_object* v___f_448_; lean_object* v___f_449_; lean_object* v___f_450_; 
v_toApplicative_445_ = lean_ctor_get(v_inst_443_, 0);
lean_inc_ref(v_toApplicative_445_);
v_toBind_446_ = lean_ctor_get(v_inst_443_, 1);
lean_inc_n(v_toBind_446_, 2);
lean_dec_ref(v_inst_443_);
v_toPure_447_ = lean_ctor_get(v_toApplicative_445_, 1);
lean_inc(v_toPure_447_);
lean_dec_ref(v_toApplicative_445_);
v___f_448_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_448_, 0, v_inst_442_);
lean_closure_set(v___f_448_, 1, v_toBind_446_);
v___f_449_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_449_, 0, v_toPure_447_);
v___f_450_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_450_, 0, v_toBind_446_);
lean_closure_set(v___f_450_, 1, v___f_449_);
lean_closure_set(v___f_450_, 2, v_inst_441_);
lean_closure_set(v___f_450_, 3, v___f_448_);
return v___f_450_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27___boxed(lean_object* v_m_451_, lean_object* v_n_452_, lean_object* v_00_u03b1_453_, lean_object* v_00_u03b2_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_inst_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Std_IterM_Total_instForIn_x27(v_m_451_, v_n_452_, v_00_u03b1_453_, v_00_u03b2_454_, v_inst_455_, v_inst_456_, v_inst_457_, v_inst_458_, v_inst_459_);
lean_dec(v_inst_455_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop___redArg(lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_inst_463_){
_start:
{
lean_object* v_toApplicative_464_; lean_object* v_toBind_465_; lean_object* v_toPure_466_; lean_object* v___f_467_; lean_object* v___f_468_; lean_object* v___f_469_; lean_object* v___f_470_; 
v_toApplicative_464_ = lean_ctor_get(v_inst_463_, 0);
lean_inc_ref(v_toApplicative_464_);
v_toBind_465_ = lean_ctor_get(v_inst_463_, 1);
lean_inc_n(v_toBind_465_, 2);
lean_dec_ref(v_inst_463_);
v_toPure_466_ = lean_ctor_get(v_toApplicative_464_, 1);
lean_inc(v_toPure_466_);
lean_dec_ref(v_toApplicative_464_);
v___f_467_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_467_, 0, v_inst_462_);
lean_closure_set(v___f_467_, 1, v_toBind_465_);
v___f_468_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_468_, 0, v_toPure_466_);
v___f_469_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_469_, 0, v_toBind_465_);
lean_closure_set(v___f_469_, 1, v___f_468_);
lean_closure_set(v___f_469_, 2, v_inst_461_);
lean_closure_set(v___f_469_, 3, v___f_467_);
v___f_470_ = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(v___f_470_, 0, v___f_469_);
return v___f_470_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop(lean_object* v_m_471_, lean_object* v_n_472_, lean_object* v_00_u03b1_473_, lean_object* v_00_u03b2_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_inst_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Std_IterM_Partial_instForInOfIteratorLoop___redArg(v_inst_476_, v_inst_477_, v_inst_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop___boxed(lean_object* v_m_480_, lean_object* v_n_481_, lean_object* v_00_u03b1_482_, lean_object* v_00_u03b2_483_, lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_inst_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Std_IterM_Partial_instForInOfIteratorLoop(v_m_480_, v_n_481_, v_00_u03b1_482_, v_00_u03b2_483_, v_inst_484_, v_inst_485_, v_inst_486_, v_inst_487_);
lean_dec(v_inst_484_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___redArg(lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_inst_491_){
_start:
{
lean_object* v_toApplicative_492_; lean_object* v_toBind_493_; lean_object* v_toPure_494_; lean_object* v___f_495_; lean_object* v___f_496_; lean_object* v___f_497_; lean_object* v___f_498_; 
v_toApplicative_492_ = lean_ctor_get(v_inst_491_, 0);
lean_inc_ref(v_toApplicative_492_);
v_toBind_493_ = lean_ctor_get(v_inst_491_, 1);
lean_inc_n(v_toBind_493_, 2);
lean_dec_ref(v_inst_491_);
v_toPure_494_ = lean_ctor_get(v_toApplicative_492_, 1);
lean_inc(v_toPure_494_);
lean_dec_ref(v_toApplicative_492_);
v___f_495_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_495_, 0, v_inst_490_);
lean_closure_set(v___f_495_, 1, v_toBind_493_);
v___f_496_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_496_, 0, v_toPure_494_);
v___f_497_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_497_, 0, v_toBind_493_);
lean_closure_set(v___f_497_, 1, v___f_496_);
lean_closure_set(v___f_497_, 2, v_inst_489_);
lean_closure_set(v___f_497_, 3, v___f_495_);
v___f_498_ = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(v___f_498_, 0, v___f_497_);
return v___f_498_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite(lean_object* v_m_499_, lean_object* v_n_500_, lean_object* v_00_u03b1_501_, lean_object* v_00_u03b2_502_, lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_inst_505_, lean_object* v_inst_506_, lean_object* v_inst_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___redArg(v_inst_504_, v_inst_505_, v_inst_506_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___boxed(lean_object* v_m_509_, lean_object* v_n_510_, lean_object* v_00_u03b1_511_, lean_object* v_00_u03b2_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_inst_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite(v_m_509_, v_n_510_, v_00_u03b1_511_, v_00_u03b2_512_, v_inst_513_, v_inst_514_, v_inst_515_, v_inst_516_, v_inst_517_);
lean_dec(v_inst_513_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1(lean_object* v_toPure_519_, lean_object* v_____do__lift_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = lean_apply_2(v_toPure_519_, lean_box(0), v_____do__lift_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__0(lean_object* v___x_522_, lean_object* v_toPure_523_, lean_object* v_____r_524_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_522_);
v___x_526_ = lean_apply_2(v_toPure_523_, lean_box(0), v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__2(lean_object* v_f_527_, lean_object* v_toBind_528_, lean_object* v___f_529_, lean_object* v___f_530_, lean_object* v_x1_531_, lean_object* v_x2_532_, lean_object* v_x3_533_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_534_ = lean_apply_1(v_f_527_, v_x1_531_);
lean_inc(v_toBind_528_);
v___x_535_ = lean_apply_4(v_toBind_528_, lean_box(0), lean_box(0), v___x_534_, v___f_529_);
v___x_536_ = lean_apply_4(v_toBind_528_, lean_box(0), lean_box(0), v___x_535_, v___f_530_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3(lean_object* v_toPure_537_, lean_object* v_toBind_538_, lean_object* v___f_539_, lean_object* v_inst_540_, lean_object* v___f_541_, lean_object* v_it_542_, lean_object* v_f_543_){
_start:
{
lean_object* v___x_544_; lean_object* v___f_545_; lean_object* v___f_546_; lean_object* v___x_547_; 
v___x_544_ = lean_box(0);
v___f_545_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__0), 3, 2);
lean_closure_set(v___f_545_, 0, v___x_544_);
lean_closure_set(v___f_545_, 1, v_toPure_537_);
v___f_546_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__2), 7, 4);
lean_closure_set(v___f_546_, 0, v_f_543_);
lean_closure_set(v___f_546_, 1, v_toBind_538_);
lean_closure_set(v___f_546_, 2, v___f_545_);
lean_closure_set(v___f_546_, 3, v___f_539_);
v___x_547_ = lean_apply_6(v_inst_540_, v___f_541_, lean_box(0), lean_box(0), v_it_542_, v___x_544_, v___f_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg(lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_inst_550_){
_start:
{
lean_object* v_toApplicative_551_; lean_object* v_toBind_552_; lean_object* v_toPure_553_; lean_object* v___f_554_; lean_object* v___f_555_; lean_object* v___f_556_; 
v_toApplicative_551_ = lean_ctor_get(v_inst_549_, 0);
lean_inc_ref(v_toApplicative_551_);
v_toBind_552_ = lean_ctor_get(v_inst_549_, 1);
lean_inc_n(v_toBind_552_, 2);
lean_dec_ref(v_inst_549_);
v_toPure_553_ = lean_ctor_get(v_toApplicative_551_, 1);
lean_inc_n(v_toPure_553_, 2);
lean_dec_ref(v_toApplicative_551_);
v___f_554_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_554_, 0, v_inst_550_);
lean_closure_set(v___f_554_, 1, v_toBind_552_);
v___f_555_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_555_, 0, v_toPure_553_);
v___f_556_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3), 7, 5);
lean_closure_set(v___f_556_, 0, v_toPure_553_);
lean_closure_set(v___f_556_, 1, v_toBind_552_);
lean_closure_set(v___f_556_, 2, v___f_555_);
lean_closure_set(v___f_556_, 3, v_inst_548_);
lean_closure_set(v___f_556_, 4, v___f_554_);
return v___f_556_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop(lean_object* v_m_557_, lean_object* v_n_558_, lean_object* v_00_u03b1_559_, lean_object* v_00_u03b2_560_, lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_inst_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_IterM_instForMOfIteratorLoop___redArg(v_inst_562_, v_inst_563_, v_inst_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___boxed(lean_object* v_m_566_, lean_object* v_n_567_, lean_object* v_00_u03b1_568_, lean_object* v_00_u03b2_569_, lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_inst_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Std_IterM_instForMOfIteratorLoop(v_m_566_, v_n_567_, v_00_u03b1_568_, v_00_u03b2_569_, v_inst_570_, v_inst_571_, v_inst_572_, v_inst_573_);
lean_dec(v_inst_570_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop___redArg(lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_inst_577_){
_start:
{
lean_object* v_toApplicative_578_; lean_object* v_toBind_579_; lean_object* v_toPure_580_; lean_object* v___f_581_; lean_object* v___f_582_; lean_object* v___f_583_; 
v_toApplicative_578_ = lean_ctor_get(v_inst_575_, 0);
lean_inc_ref(v_toApplicative_578_);
v_toBind_579_ = lean_ctor_get(v_inst_575_, 1);
lean_inc_n(v_toBind_579_, 2);
lean_dec_ref(v_inst_575_);
v_toPure_580_ = lean_ctor_get(v_toApplicative_578_, 1);
lean_inc_n(v_toPure_580_, 2);
lean_dec_ref(v_toApplicative_578_);
v___f_581_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_581_, 0, v_inst_577_);
lean_closure_set(v___f_581_, 1, v_toBind_579_);
v___f_582_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_582_, 0, v_toPure_580_);
v___f_583_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3), 7, 5);
lean_closure_set(v___f_583_, 0, v_toPure_580_);
lean_closure_set(v___f_583_, 1, v_toBind_579_);
lean_closure_set(v___f_583_, 2, v___f_582_);
lean_closure_set(v___f_583_, 3, v_inst_576_);
lean_closure_set(v___f_583_, 4, v___f_581_);
return v___f_583_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop(lean_object* v_m_584_, lean_object* v_n_585_, lean_object* v_00_u03b1_586_, lean_object* v_00_u03b2_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_inst_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Std_IterM_Partial_instForMOfItreratorLoop___redArg(v_inst_588_, v_inst_590_, v_inst_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop___boxed(lean_object* v_m_593_, lean_object* v_n_594_, lean_object* v_00_u03b1_595_, lean_object* v_00_u03b2_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_inst_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_IterM_Partial_instForMOfItreratorLoop(v_m_593_, v_n_594_, v_00_u03b1_595_, v_00_u03b2_596_, v_inst_597_, v_inst_598_, v_inst_599_, v_inst_600_);
lean_dec(v_inst_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___redArg(lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_inst_604_){
_start:
{
lean_object* v_toApplicative_605_; lean_object* v_toBind_606_; lean_object* v_toPure_607_; lean_object* v___f_608_; lean_object* v___f_609_; lean_object* v___f_610_; 
v_toApplicative_605_ = lean_ctor_get(v_inst_603_, 0);
lean_inc_ref(v_toApplicative_605_);
v_toBind_606_ = lean_ctor_get(v_inst_603_, 1);
lean_inc_n(v_toBind_606_, 2);
lean_dec_ref(v_inst_603_);
v_toPure_607_ = lean_ctor_get(v_toApplicative_605_, 1);
lean_inc_n(v_toPure_607_, 2);
lean_dec_ref(v_toApplicative_605_);
v___f_608_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_608_, 0, v_inst_604_);
lean_closure_set(v___f_608_, 1, v_toBind_606_);
v___f_609_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_609_, 0, v_toPure_607_);
v___f_610_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3), 7, 5);
lean_closure_set(v___f_610_, 0, v_toPure_607_);
lean_closure_set(v___f_610_, 1, v_toBind_606_);
lean_closure_set(v___f_610_, 2, v___f_609_);
lean_closure_set(v___f_610_, 3, v_inst_602_);
lean_closure_set(v___f_610_, 4, v___f_608_);
return v___f_610_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite(lean_object* v_m_611_, lean_object* v_n_612_, lean_object* v_00_u03b1_613_, lean_object* v_00_u03b2_614_, lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_inst_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___redArg(v_inst_616_, v_inst_617_, v_inst_618_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___boxed(lean_object* v_m_621_, lean_object* v_n_622_, lean_object* v_00_u03b1_623_, lean_object* v_00_u03b2_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_inst_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite(v_m_621_, v_n_622_, v_00_u03b1_623_, v_00_u03b2_624_, v_inst_625_, v_inst_626_, v_inst_627_, v_inst_628_, v_inst_629_);
lean_dec(v_inst_625_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg___lam__0(lean_object* v_a_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_632_, 0, v_a_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg___lam__3(lean_object* v_toFunctor_633_, lean_object* v_f_634_, lean_object* v___f_635_, lean_object* v_toBind_636_, lean_object* v___f_637_, lean_object* v_x1_638_, lean_object* v_x2_639_, lean_object* v_x3_640_){
_start:
{
lean_object* v_map_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_map_641_ = lean_ctor_get(v_toFunctor_633_, 0);
lean_inc(v_map_641_);
lean_dec_ref(v_toFunctor_633_);
v___x_642_ = lean_apply_2(v_f_634_, v_x3_640_, v_x1_638_);
v___x_643_ = lean_apply_4(v_map_641_, lean_box(0), lean_box(0), v___f_635_, v___x_642_);
v___x_644_ = lean_apply_4(v_toBind_636_, lean_box(0), lean_box(0), v___x_643_, v___f_637_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg(lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_f_649_, lean_object* v_init_650_, lean_object* v_it_651_){
_start:
{
lean_object* v_toApplicative_652_; lean_object* v_toBind_653_; lean_object* v_toFunctor_654_; lean_object* v_toPure_655_; lean_object* v___f_656_; lean_object* v___f_657_; lean_object* v___f_658_; lean_object* v___f_659_; lean_object* v___x_660_; 
v_toApplicative_652_ = lean_ctor_get(v_inst_646_, 0);
lean_inc_ref(v_toApplicative_652_);
v_toBind_653_ = lean_ctor_get(v_inst_646_, 1);
lean_inc_n(v_toBind_653_, 2);
lean_dec_ref(v_inst_646_);
v_toFunctor_654_ = lean_ctor_get(v_toApplicative_652_, 0);
lean_inc_ref(v_toFunctor_654_);
v_toPure_655_ = lean_ctor_get(v_toApplicative_652_, 1);
lean_inc(v_toPure_655_);
lean_dec_ref(v_toApplicative_652_);
v___f_656_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
v___f_657_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_657_, 0, v_inst_648_);
lean_closure_set(v___f_657_, 1, v_toBind_653_);
v___f_658_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_658_, 0, v_toPure_655_);
v___f_659_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_659_, 0, v_toFunctor_654_);
lean_closure_set(v___f_659_, 1, v_f_649_);
lean_closure_set(v___f_659_, 2, v___f_656_);
lean_closure_set(v___f_659_, 3, v_toBind_653_);
lean_closure_set(v___f_659_, 4, v___f_658_);
v___x_660_ = lean_apply_6(v_inst_647_, v___f_657_, lean_box(0), lean_box(0), v_it_651_, v_init_650_, v___f_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM(lean_object* v_m_661_, lean_object* v_n_662_, lean_object* v_inst_663_, lean_object* v_00_u03b1_664_, lean_object* v_00_u03b2_665_, lean_object* v_00_u03b3_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_f_670_, lean_object* v_init_671_, lean_object* v_it_672_){
_start:
{
lean_object* v_toApplicative_673_; lean_object* v_toBind_674_; lean_object* v_toFunctor_675_; lean_object* v_toPure_676_; lean_object* v___f_677_; lean_object* v___f_678_; lean_object* v___f_679_; lean_object* v___f_680_; lean_object* v___x_681_; 
v_toApplicative_673_ = lean_ctor_get(v_inst_663_, 0);
lean_inc_ref(v_toApplicative_673_);
v_toBind_674_ = lean_ctor_get(v_inst_663_, 1);
lean_inc_n(v_toBind_674_, 2);
lean_dec_ref(v_inst_663_);
v_toFunctor_675_ = lean_ctor_get(v_toApplicative_673_, 0);
lean_inc_ref(v_toFunctor_675_);
v_toPure_676_ = lean_ctor_get(v_toApplicative_673_, 1);
lean_inc(v_toPure_676_);
lean_dec_ref(v_toApplicative_673_);
v___f_677_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
v___f_678_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_678_, 0, v_inst_669_);
lean_closure_set(v___f_678_, 1, v_toBind_674_);
v___f_679_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_679_, 0, v_toPure_676_);
v___f_680_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_680_, 0, v_toFunctor_675_);
lean_closure_set(v___f_680_, 1, v_f_670_);
lean_closure_set(v___f_680_, 2, v___f_677_);
lean_closure_set(v___f_680_, 3, v_toBind_674_);
lean_closure_set(v___f_680_, 4, v___f_679_);
v___x_681_ = lean_apply_6(v_inst_668_, v___f_678_, lean_box(0), lean_box(0), v_it_672_, v_init_671_, v___f_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___boxed(lean_object* v_m_682_, lean_object* v_n_683_, lean_object* v_inst_684_, lean_object* v_00_u03b1_685_, lean_object* v_00_u03b2_686_, lean_object* v_00_u03b3_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_f_691_, lean_object* v_init_692_, lean_object* v_it_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Std_IterM_foldM(v_m_682_, v_n_683_, v_inst_684_, v_00_u03b1_685_, v_00_u03b2_686_, v_00_u03b3_687_, v_inst_688_, v_inst_689_, v_inst_690_, v_f_691_, v_init_692_, v_it_693_);
lean_dec(v_inst_688_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM___redArg(lean_object* v_inst_695_, lean_object* v_inst_696_, lean_object* v_inst_697_, lean_object* v_f_698_, lean_object* v_init_699_, lean_object* v_it_700_){
_start:
{
lean_object* v_toApplicative_701_; lean_object* v_toBind_702_; lean_object* v_toFunctor_703_; lean_object* v_toPure_704_; lean_object* v___f_705_; lean_object* v___f_706_; lean_object* v___f_707_; lean_object* v___f_708_; lean_object* v___x_709_; 
v_toApplicative_701_ = lean_ctor_get(v_inst_695_, 0);
lean_inc_ref(v_toApplicative_701_);
v_toBind_702_ = lean_ctor_get(v_inst_695_, 1);
lean_inc_n(v_toBind_702_, 2);
lean_dec_ref(v_inst_695_);
v_toFunctor_703_ = lean_ctor_get(v_toApplicative_701_, 0);
lean_inc_ref(v_toFunctor_703_);
v_toPure_704_ = lean_ctor_get(v_toApplicative_701_, 1);
lean_inc(v_toPure_704_);
lean_dec_ref(v_toApplicative_701_);
v___f_705_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
v___f_706_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_706_, 0, v_inst_697_);
lean_closure_set(v___f_706_, 1, v_toBind_702_);
v___f_707_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_707_, 0, v_toPure_704_);
v___f_708_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_708_, 0, v_toFunctor_703_);
lean_closure_set(v___f_708_, 1, v_f_698_);
lean_closure_set(v___f_708_, 2, v___f_705_);
lean_closure_set(v___f_708_, 3, v_toBind_702_);
lean_closure_set(v___f_708_, 4, v___f_707_);
v___x_709_ = lean_apply_6(v_inst_696_, v___f_706_, lean_box(0), lean_box(0), v_it_700_, v_init_699_, v___f_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM(lean_object* v_m_710_, lean_object* v_n_711_, lean_object* v_inst_712_, lean_object* v_00_u03b1_713_, lean_object* v_00_u03b2_714_, lean_object* v_00_u03b3_715_, lean_object* v_inst_716_, lean_object* v_inst_717_, lean_object* v_inst_718_, lean_object* v_f_719_, lean_object* v_init_720_, lean_object* v_it_721_){
_start:
{
lean_object* v_toApplicative_722_; lean_object* v_toBind_723_; lean_object* v_toFunctor_724_; lean_object* v_toPure_725_; lean_object* v___f_726_; lean_object* v___f_727_; lean_object* v___f_728_; lean_object* v___f_729_; lean_object* v___x_730_; 
v_toApplicative_722_ = lean_ctor_get(v_inst_712_, 0);
lean_inc_ref(v_toApplicative_722_);
v_toBind_723_ = lean_ctor_get(v_inst_712_, 1);
lean_inc_n(v_toBind_723_, 2);
lean_dec_ref(v_inst_712_);
v_toFunctor_724_ = lean_ctor_get(v_toApplicative_722_, 0);
lean_inc_ref(v_toFunctor_724_);
v_toPure_725_ = lean_ctor_get(v_toApplicative_722_, 1);
lean_inc(v_toPure_725_);
lean_dec_ref(v_toApplicative_722_);
v___f_726_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
v___f_727_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_727_, 0, v_inst_718_);
lean_closure_set(v___f_727_, 1, v_toBind_723_);
v___f_728_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_728_, 0, v_toPure_725_);
v___f_729_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_729_, 0, v_toFunctor_724_);
lean_closure_set(v___f_729_, 1, v_f_719_);
lean_closure_set(v___f_729_, 2, v___f_726_);
lean_closure_set(v___f_729_, 3, v_toBind_723_);
lean_closure_set(v___f_729_, 4, v___f_728_);
v___x_730_ = lean_apply_6(v_inst_717_, v___f_727_, lean_box(0), lean_box(0), v_it_721_, v_init_720_, v___f_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM___boxed(lean_object* v_m_731_, lean_object* v_n_732_, lean_object* v_inst_733_, lean_object* v_00_u03b1_734_, lean_object* v_00_u03b2_735_, lean_object* v_00_u03b3_736_, lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_f_740_, lean_object* v_init_741_, lean_object* v_it_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Std_IterM_Partial_foldM(v_m_731_, v_n_732_, v_inst_733_, v_00_u03b1_734_, v_00_u03b2_735_, v_00_u03b3_736_, v_inst_737_, v_inst_738_, v_inst_739_, v_f_740_, v_init_741_, v_it_742_);
lean_dec(v_inst_737_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM___redArg(lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_f_747_, lean_object* v_init_748_, lean_object* v_it_749_){
_start:
{
lean_object* v_toApplicative_750_; lean_object* v_toBind_751_; lean_object* v_toFunctor_752_; lean_object* v_toPure_753_; lean_object* v___f_754_; lean_object* v___f_755_; lean_object* v___f_756_; lean_object* v___f_757_; lean_object* v___x_758_; 
v_toApplicative_750_ = lean_ctor_get(v_inst_744_, 0);
lean_inc_ref(v_toApplicative_750_);
v_toBind_751_ = lean_ctor_get(v_inst_744_, 1);
lean_inc_n(v_toBind_751_, 2);
lean_dec_ref(v_inst_744_);
v_toFunctor_752_ = lean_ctor_get(v_toApplicative_750_, 0);
lean_inc_ref(v_toFunctor_752_);
v_toPure_753_ = lean_ctor_get(v_toApplicative_750_, 1);
lean_inc(v_toPure_753_);
lean_dec_ref(v_toApplicative_750_);
v___f_754_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
v___f_755_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_755_, 0, v_inst_746_);
lean_closure_set(v___f_755_, 1, v_toBind_751_);
v___f_756_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_756_, 0, v_toPure_753_);
v___f_757_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_757_, 0, v_toFunctor_752_);
lean_closure_set(v___f_757_, 1, v_f_747_);
lean_closure_set(v___f_757_, 2, v___f_754_);
lean_closure_set(v___f_757_, 3, v_toBind_751_);
lean_closure_set(v___f_757_, 4, v___f_756_);
v___x_758_ = lean_apply_6(v_inst_745_, v___f_755_, lean_box(0), lean_box(0), v_it_749_, v_init_748_, v___f_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM(lean_object* v_m_759_, lean_object* v_n_760_, lean_object* v_inst_761_, lean_object* v_00_u03b1_762_, lean_object* v_00_u03b2_763_, lean_object* v_00_u03b3_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_inst_768_, lean_object* v_f_769_, lean_object* v_init_770_, lean_object* v_it_771_){
_start:
{
lean_object* v_toApplicative_772_; lean_object* v_toBind_773_; lean_object* v_toFunctor_774_; lean_object* v_toPure_775_; lean_object* v___f_776_; lean_object* v___f_777_; lean_object* v___f_778_; lean_object* v___f_779_; lean_object* v___x_780_; 
v_toApplicative_772_ = lean_ctor_get(v_inst_761_, 0);
lean_inc_ref(v_toApplicative_772_);
v_toBind_773_ = lean_ctor_get(v_inst_761_, 1);
lean_inc_n(v_toBind_773_, 2);
lean_dec_ref(v_inst_761_);
v_toFunctor_774_ = lean_ctor_get(v_toApplicative_772_, 0);
lean_inc_ref(v_toFunctor_774_);
v_toPure_775_ = lean_ctor_get(v_toApplicative_772_, 1);
lean_inc(v_toPure_775_);
lean_dec_ref(v_toApplicative_772_);
v___f_776_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
v___f_777_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_777_, 0, v_inst_767_);
lean_closure_set(v___f_777_, 1, v_toBind_773_);
v___f_778_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_778_, 0, v_toPure_775_);
v___f_779_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_779_, 0, v_toFunctor_774_);
lean_closure_set(v___f_779_, 1, v_f_769_);
lean_closure_set(v___f_779_, 2, v___f_776_);
lean_closure_set(v___f_779_, 3, v_toBind_773_);
lean_closure_set(v___f_779_, 4, v___f_778_);
v___x_780_ = lean_apply_6(v_inst_766_, v___f_777_, lean_box(0), lean_box(0), v_it_771_, v_init_770_, v___f_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM___boxed(lean_object* v_m_781_, lean_object* v_n_782_, lean_object* v_inst_783_, lean_object* v_00_u03b1_784_, lean_object* v_00_u03b2_785_, lean_object* v_00_u03b3_786_, lean_object* v_inst_787_, lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_f_791_, lean_object* v_init_792_, lean_object* v_it_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Std_IterM_Total_foldM(v_m_781_, v_n_782_, v_inst_783_, v_00_u03b1_784_, v_00_u03b2_785_, v_00_u03b3_786_, v_inst_787_, v_inst_788_, v_inst_789_, v_inst_790_, v_f_791_, v_init_792_, v_it_793_);
lean_dec(v_inst_787_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg___lam__0(lean_object* v_toBind_795_, lean_object* v_x_796_, lean_object* v_x_797_, lean_object* v_f_798_, lean_object* v_x_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = lean_apply_4(v_toBind_795_, lean_box(0), lean_box(0), v_x_799_, v_f_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg___lam__2(lean_object* v_f_801_, lean_object* v_toPure_802_, lean_object* v_toBind_803_, lean_object* v___f_804_, lean_object* v_x1_805_, lean_object* v_x2_806_, lean_object* v_x3_807_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_808_ = lean_apply_2(v_f_801_, v_x3_807_, v_x1_805_);
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
v___x_810_ = lean_apply_2(v_toPure_802_, lean_box(0), v___x_809_);
v___x_811_ = lean_apply_4(v_toBind_803_, lean_box(0), lean_box(0), v___x_810_, v___f_804_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg(lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_f_814_, lean_object* v_init_815_, lean_object* v_it_816_){
_start:
{
lean_object* v_toApplicative_817_; lean_object* v_toBind_818_; lean_object* v_toPure_819_; lean_object* v___f_820_; lean_object* v___f_821_; lean_object* v___f_822_; lean_object* v___x_823_; 
v_toApplicative_817_ = lean_ctor_get(v_inst_812_, 0);
lean_inc_ref(v_toApplicative_817_);
v_toBind_818_ = lean_ctor_get(v_inst_812_, 1);
lean_inc_n(v_toBind_818_, 2);
lean_dec_ref(v_inst_812_);
v_toPure_819_ = lean_ctor_get(v_toApplicative_817_, 1);
lean_inc_n(v_toPure_819_, 2);
lean_dec_ref(v_toApplicative_817_);
v___f_820_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_820_, 0, v_toBind_818_);
v___f_821_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_821_, 0, v_toPure_819_);
v___f_822_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_822_, 0, v_f_814_);
lean_closure_set(v___f_822_, 1, v_toPure_819_);
lean_closure_set(v___f_822_, 2, v_toBind_818_);
lean_closure_set(v___f_822_, 3, v___f_821_);
v___x_823_ = lean_apply_6(v_inst_813_, v___f_820_, lean_box(0), lean_box(0), v_it_816_, v_init_815_, v___f_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold(lean_object* v_m_824_, lean_object* v_00_u03b1_825_, lean_object* v_00_u03b2_826_, lean_object* v_00_u03b3_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_inst_830_, lean_object* v_f_831_, lean_object* v_init_832_, lean_object* v_it_833_){
_start:
{
lean_object* v_toApplicative_834_; lean_object* v_toBind_835_; lean_object* v_toPure_836_; lean_object* v___f_837_; lean_object* v___f_838_; lean_object* v___f_839_; lean_object* v___x_840_; 
v_toApplicative_834_ = lean_ctor_get(v_inst_828_, 0);
lean_inc_ref(v_toApplicative_834_);
v_toBind_835_ = lean_ctor_get(v_inst_828_, 1);
lean_inc_n(v_toBind_835_, 2);
lean_dec_ref(v_inst_828_);
v_toPure_836_ = lean_ctor_get(v_toApplicative_834_, 1);
lean_inc_n(v_toPure_836_, 2);
lean_dec_ref(v_toApplicative_834_);
v___f_837_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_837_, 0, v_toBind_835_);
v___f_838_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_838_, 0, v_toPure_836_);
v___f_839_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_839_, 0, v_f_831_);
lean_closure_set(v___f_839_, 1, v_toPure_836_);
lean_closure_set(v___f_839_, 2, v_toBind_835_);
lean_closure_set(v___f_839_, 3, v___f_838_);
v___x_840_ = lean_apply_6(v_inst_830_, v___f_837_, lean_box(0), lean_box(0), v_it_833_, v_init_832_, v___f_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___boxed(lean_object* v_m_841_, lean_object* v_00_u03b1_842_, lean_object* v_00_u03b2_843_, lean_object* v_00_u03b3_844_, lean_object* v_inst_845_, lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_f_848_, lean_object* v_init_849_, lean_object* v_it_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Std_IterM_fold(v_m_841_, v_00_u03b1_842_, v_00_u03b2_843_, v_00_u03b3_844_, v_inst_845_, v_inst_846_, v_inst_847_, v_f_848_, v_init_849_, v_it_850_);
lean_dec(v_inst_846_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold___redArg(lean_object* v_inst_852_, lean_object* v_inst_853_, lean_object* v_f_854_, lean_object* v_init_855_, lean_object* v_it_856_){
_start:
{
lean_object* v_toApplicative_857_; lean_object* v_toBind_858_; lean_object* v_toPure_859_; lean_object* v___f_860_; lean_object* v___f_861_; lean_object* v___f_862_; lean_object* v___x_863_; 
v_toApplicative_857_ = lean_ctor_get(v_inst_852_, 0);
lean_inc_ref(v_toApplicative_857_);
v_toBind_858_ = lean_ctor_get(v_inst_852_, 1);
lean_inc_n(v_toBind_858_, 2);
lean_dec_ref(v_inst_852_);
v_toPure_859_ = lean_ctor_get(v_toApplicative_857_, 1);
lean_inc_n(v_toPure_859_, 2);
lean_dec_ref(v_toApplicative_857_);
v___f_860_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_860_, 0, v_toBind_858_);
v___f_861_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_861_, 0, v_toPure_859_);
v___f_862_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_862_, 0, v_f_854_);
lean_closure_set(v___f_862_, 1, v_toPure_859_);
lean_closure_set(v___f_862_, 2, v_toBind_858_);
lean_closure_set(v___f_862_, 3, v___f_861_);
v___x_863_ = lean_apply_6(v_inst_853_, v___f_860_, lean_box(0), lean_box(0), v_it_856_, v_init_855_, v___f_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold(lean_object* v_m_864_, lean_object* v_00_u03b1_865_, lean_object* v_00_u03b2_866_, lean_object* v_00_u03b3_867_, lean_object* v_inst_868_, lean_object* v_inst_869_, lean_object* v_inst_870_, lean_object* v_f_871_, lean_object* v_init_872_, lean_object* v_it_873_){
_start:
{
lean_object* v_toApplicative_874_; lean_object* v_toBind_875_; lean_object* v_toPure_876_; lean_object* v___f_877_; lean_object* v___f_878_; lean_object* v___f_879_; lean_object* v___x_880_; 
v_toApplicative_874_ = lean_ctor_get(v_inst_868_, 0);
lean_inc_ref(v_toApplicative_874_);
v_toBind_875_ = lean_ctor_get(v_inst_868_, 1);
lean_inc_n(v_toBind_875_, 2);
lean_dec_ref(v_inst_868_);
v_toPure_876_ = lean_ctor_get(v_toApplicative_874_, 1);
lean_inc_n(v_toPure_876_, 2);
lean_dec_ref(v_toApplicative_874_);
v___f_877_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_877_, 0, v_toBind_875_);
v___f_878_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_878_, 0, v_toPure_876_);
v___f_879_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_879_, 0, v_f_871_);
lean_closure_set(v___f_879_, 1, v_toPure_876_);
lean_closure_set(v___f_879_, 2, v_toBind_875_);
lean_closure_set(v___f_879_, 3, v___f_878_);
v___x_880_ = lean_apply_6(v_inst_870_, v___f_877_, lean_box(0), lean_box(0), v_it_873_, v_init_872_, v___f_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold___boxed(lean_object* v_m_881_, lean_object* v_00_u03b1_882_, lean_object* v_00_u03b2_883_, lean_object* v_00_u03b3_884_, lean_object* v_inst_885_, lean_object* v_inst_886_, lean_object* v_inst_887_, lean_object* v_f_888_, lean_object* v_init_889_, lean_object* v_it_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Std_IterM_Partial_fold(v_m_881_, v_00_u03b1_882_, v_00_u03b2_883_, v_00_u03b3_884_, v_inst_885_, v_inst_886_, v_inst_887_, v_f_888_, v_init_889_, v_it_890_);
lean_dec(v_inst_886_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold___redArg(lean_object* v_inst_892_, lean_object* v_inst_893_, lean_object* v_f_894_, lean_object* v_init_895_, lean_object* v_it_896_){
_start:
{
lean_object* v_toApplicative_897_; lean_object* v_toBind_898_; lean_object* v_toPure_899_; lean_object* v___f_900_; lean_object* v___f_901_; lean_object* v___f_902_; lean_object* v___x_903_; 
v_toApplicative_897_ = lean_ctor_get(v_inst_892_, 0);
lean_inc_ref(v_toApplicative_897_);
v_toBind_898_ = lean_ctor_get(v_inst_892_, 1);
lean_inc_n(v_toBind_898_, 2);
lean_dec_ref(v_inst_892_);
v_toPure_899_ = lean_ctor_get(v_toApplicative_897_, 1);
lean_inc_n(v_toPure_899_, 2);
lean_dec_ref(v_toApplicative_897_);
v___f_900_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_900_, 0, v_toBind_898_);
v___f_901_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_901_, 0, v_toPure_899_);
v___f_902_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_902_, 0, v_f_894_);
lean_closure_set(v___f_902_, 1, v_toPure_899_);
lean_closure_set(v___f_902_, 2, v_toBind_898_);
lean_closure_set(v___f_902_, 3, v___f_901_);
v___x_903_ = lean_apply_6(v_inst_893_, v___f_900_, lean_box(0), lean_box(0), v_it_896_, v_init_895_, v___f_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold(lean_object* v_m_904_, lean_object* v_00_u03b1_905_, lean_object* v_00_u03b2_906_, lean_object* v_00_u03b3_907_, lean_object* v_inst_908_, lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_inst_911_, lean_object* v_f_912_, lean_object* v_init_913_, lean_object* v_it_914_){
_start:
{
lean_object* v_toApplicative_915_; lean_object* v_toBind_916_; lean_object* v_toPure_917_; lean_object* v___f_918_; lean_object* v___f_919_; lean_object* v___f_920_; lean_object* v___x_921_; 
v_toApplicative_915_ = lean_ctor_get(v_inst_908_, 0);
lean_inc_ref(v_toApplicative_915_);
v_toBind_916_ = lean_ctor_get(v_inst_908_, 1);
lean_inc_n(v_toBind_916_, 2);
lean_dec_ref(v_inst_908_);
v_toPure_917_ = lean_ctor_get(v_toApplicative_915_, 1);
lean_inc_n(v_toPure_917_, 2);
lean_dec_ref(v_toApplicative_915_);
v___f_918_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_918_, 0, v_toBind_916_);
v___f_919_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_919_, 0, v_toPure_917_);
v___f_920_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_920_, 0, v_f_912_);
lean_closure_set(v___f_920_, 1, v_toPure_917_);
lean_closure_set(v___f_920_, 2, v_toBind_916_);
lean_closure_set(v___f_920_, 3, v___f_919_);
v___x_921_ = lean_apply_6(v_inst_910_, v___f_918_, lean_box(0), lean_box(0), v_it_914_, v_init_913_, v___f_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold___boxed(lean_object* v_m_922_, lean_object* v_00_u03b1_923_, lean_object* v_00_u03b2_924_, lean_object* v_00_u03b3_925_, lean_object* v_inst_926_, lean_object* v_inst_927_, lean_object* v_inst_928_, lean_object* v_inst_929_, lean_object* v_f_930_, lean_object* v_init_931_, lean_object* v_it_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Std_IterM_Total_fold(v_m_922_, v_00_u03b1_923_, v_00_u03b2_924_, v_00_u03b3_925_, v_inst_926_, v_inst_927_, v_inst_928_, v_inst_929_, v_f_930_, v_init_931_, v_it_932_);
lean_dec(v_inst_927_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg___lam__2(lean_object* v___x_934_, lean_object* v_toPure_935_, lean_object* v_toBind_936_, lean_object* v___f_937_, lean_object* v_x1_938_, lean_object* v_x2_939_, lean_object* v_x3_940_){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_934_);
v___x_942_ = lean_apply_2(v_toPure_935_, lean_box(0), v___x_941_);
v___x_943_ = lean_apply_4(v_toBind_936_, lean_box(0), lean_box(0), v___x_942_, v___f_937_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg___lam__2___boxed(lean_object* v___x_944_, lean_object* v_toPure_945_, lean_object* v_toBind_946_, lean_object* v___f_947_, lean_object* v_x1_948_, lean_object* v_x2_949_, lean_object* v_x3_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std_IterM_drain___redArg___lam__2(v___x_944_, v_toPure_945_, v_toBind_946_, v___f_947_, v_x1_948_, v_x2_949_, v_x3_950_);
lean_dec(v_x1_948_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg(lean_object* v_inst_952_, lean_object* v_it_953_, lean_object* v_inst_954_){
_start:
{
lean_object* v_toApplicative_955_; lean_object* v_toBind_956_; lean_object* v_toPure_957_; lean_object* v___x_958_; lean_object* v___f_959_; lean_object* v___f_960_; lean_object* v___f_961_; lean_object* v___x_962_; 
v_toApplicative_955_ = lean_ctor_get(v_inst_952_, 0);
lean_inc_ref(v_toApplicative_955_);
v_toBind_956_ = lean_ctor_get(v_inst_952_, 1);
lean_inc_n(v_toBind_956_, 2);
lean_dec_ref(v_inst_952_);
v_toPure_957_ = lean_ctor_get(v_toApplicative_955_, 1);
lean_inc_n(v_toPure_957_, 2);
lean_dec_ref(v_toApplicative_955_);
v___x_958_ = lean_box(0);
v___f_959_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_959_, 0, v_toBind_956_);
v___f_960_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_960_, 0, v_toPure_957_);
v___f_961_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_961_, 0, v___x_958_);
lean_closure_set(v___f_961_, 1, v_toPure_957_);
lean_closure_set(v___f_961_, 2, v_toBind_956_);
lean_closure_set(v___f_961_, 3, v___f_960_);
v___x_962_ = lean_apply_6(v_inst_954_, v___f_959_, lean_box(0), lean_box(0), v_it_953_, v___x_958_, v___f_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain(lean_object* v_00_u03b1_963_, lean_object* v_m_964_, lean_object* v_inst_965_, lean_object* v_00_u03b2_966_, lean_object* v_inst_967_, lean_object* v_it_968_, lean_object* v_inst_969_){
_start:
{
lean_object* v_toApplicative_970_; lean_object* v_toBind_971_; lean_object* v_toPure_972_; lean_object* v___x_973_; lean_object* v___f_974_; lean_object* v___f_975_; lean_object* v___f_976_; lean_object* v___x_977_; 
v_toApplicative_970_ = lean_ctor_get(v_inst_965_, 0);
lean_inc_ref(v_toApplicative_970_);
v_toBind_971_ = lean_ctor_get(v_inst_965_, 1);
lean_inc_n(v_toBind_971_, 2);
lean_dec_ref(v_inst_965_);
v_toPure_972_ = lean_ctor_get(v_toApplicative_970_, 1);
lean_inc_n(v_toPure_972_, 2);
lean_dec_ref(v_toApplicative_970_);
v___x_973_ = lean_box(0);
v___f_974_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_974_, 0, v_toBind_971_);
v___f_975_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_975_, 0, v_toPure_972_);
v___f_976_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_976_, 0, v___x_973_);
lean_closure_set(v___f_976_, 1, v_toPure_972_);
lean_closure_set(v___f_976_, 2, v_toBind_971_);
lean_closure_set(v___f_976_, 3, v___f_975_);
v___x_977_ = lean_apply_6(v_inst_969_, v___f_974_, lean_box(0), lean_box(0), v_it_968_, v___x_973_, v___f_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___boxed(lean_object* v_00_u03b1_978_, lean_object* v_m_979_, lean_object* v_inst_980_, lean_object* v_00_u03b2_981_, lean_object* v_inst_982_, lean_object* v_it_983_, lean_object* v_inst_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Std_IterM_drain(v_00_u03b1_978_, v_m_979_, v_inst_980_, v_00_u03b2_981_, v_inst_982_, v_it_983_, v_inst_984_);
lean_dec(v_inst_982_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain___redArg(lean_object* v_inst_986_, lean_object* v_it_987_, lean_object* v_inst_988_){
_start:
{
lean_object* v_toApplicative_989_; lean_object* v_toBind_990_; lean_object* v_toPure_991_; lean_object* v___x_992_; lean_object* v___f_993_; lean_object* v___f_994_; lean_object* v___f_995_; lean_object* v___x_996_; 
v_toApplicative_989_ = lean_ctor_get(v_inst_986_, 0);
lean_inc_ref(v_toApplicative_989_);
v_toBind_990_ = lean_ctor_get(v_inst_986_, 1);
lean_inc_n(v_toBind_990_, 2);
lean_dec_ref(v_inst_986_);
v_toPure_991_ = lean_ctor_get(v_toApplicative_989_, 1);
lean_inc_n(v_toPure_991_, 2);
lean_dec_ref(v_toApplicative_989_);
v___x_992_ = lean_box(0);
v___f_993_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_993_, 0, v_toBind_990_);
v___f_994_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_994_, 0, v_toPure_991_);
v___f_995_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_995_, 0, v___x_992_);
lean_closure_set(v___f_995_, 1, v_toPure_991_);
lean_closure_set(v___f_995_, 2, v_toBind_990_);
lean_closure_set(v___f_995_, 3, v___f_994_);
v___x_996_ = lean_apply_6(v_inst_988_, v___f_993_, lean_box(0), lean_box(0), v_it_987_, v___x_992_, v___f_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain(lean_object* v_00_u03b1_997_, lean_object* v_m_998_, lean_object* v_inst_999_, lean_object* v_00_u03b2_1000_, lean_object* v_inst_1001_, lean_object* v_it_1002_, lean_object* v_inst_1003_){
_start:
{
lean_object* v_toApplicative_1004_; lean_object* v_toBind_1005_; lean_object* v_toPure_1006_; lean_object* v___x_1007_; lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___f_1010_; lean_object* v___x_1011_; 
v_toApplicative_1004_ = lean_ctor_get(v_inst_999_, 0);
lean_inc_ref(v_toApplicative_1004_);
v_toBind_1005_ = lean_ctor_get(v_inst_999_, 1);
lean_inc_n(v_toBind_1005_, 2);
lean_dec_ref(v_inst_999_);
v_toPure_1006_ = lean_ctor_get(v_toApplicative_1004_, 1);
lean_inc_n(v_toPure_1006_, 2);
lean_dec_ref(v_toApplicative_1004_);
v___x_1007_ = lean_box(0);
v___f_1008_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1008_, 0, v_toBind_1005_);
v___f_1009_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1009_, 0, v_toPure_1006_);
v___f_1010_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1010_, 0, v___x_1007_);
lean_closure_set(v___f_1010_, 1, v_toPure_1006_);
lean_closure_set(v___f_1010_, 2, v_toBind_1005_);
lean_closure_set(v___f_1010_, 3, v___f_1009_);
v___x_1011_ = lean_apply_6(v_inst_1003_, v___f_1008_, lean_box(0), lean_box(0), v_it_1002_, v___x_1007_, v___f_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain___boxed(lean_object* v_00_u03b1_1012_, lean_object* v_m_1013_, lean_object* v_inst_1014_, lean_object* v_00_u03b2_1015_, lean_object* v_inst_1016_, lean_object* v_it_1017_, lean_object* v_inst_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Std_IterM_Partial_drain(v_00_u03b1_1012_, v_m_1013_, v_inst_1014_, v_00_u03b2_1015_, v_inst_1016_, v_it_1017_, v_inst_1018_);
lean_dec(v_inst_1016_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain___redArg(lean_object* v_inst_1020_, lean_object* v_it_1021_, lean_object* v_inst_1022_){
_start:
{
lean_object* v_toApplicative_1023_; lean_object* v_toBind_1024_; lean_object* v_toPure_1025_; lean_object* v___x_1026_; lean_object* v___f_1027_; lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v___x_1030_; 
v_toApplicative_1023_ = lean_ctor_get(v_inst_1020_, 0);
lean_inc_ref(v_toApplicative_1023_);
v_toBind_1024_ = lean_ctor_get(v_inst_1020_, 1);
lean_inc_n(v_toBind_1024_, 2);
lean_dec_ref(v_inst_1020_);
v_toPure_1025_ = lean_ctor_get(v_toApplicative_1023_, 1);
lean_inc_n(v_toPure_1025_, 2);
lean_dec_ref(v_toApplicative_1023_);
v___x_1026_ = lean_box(0);
v___f_1027_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1027_, 0, v_toBind_1024_);
v___f_1028_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1028_, 0, v_toPure_1025_);
v___f_1029_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1029_, 0, v___x_1026_);
lean_closure_set(v___f_1029_, 1, v_toPure_1025_);
lean_closure_set(v___f_1029_, 2, v_toBind_1024_);
lean_closure_set(v___f_1029_, 3, v___f_1028_);
v___x_1030_ = lean_apply_6(v_inst_1022_, v___f_1027_, lean_box(0), lean_box(0), v_it_1021_, v___x_1026_, v___f_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain(lean_object* v_00_u03b1_1031_, lean_object* v_m_1032_, lean_object* v_inst_1033_, lean_object* v_00_u03b2_1034_, lean_object* v_inst_1035_, lean_object* v_inst_1036_, lean_object* v_it_1037_, lean_object* v_inst_1038_){
_start:
{
lean_object* v_toApplicative_1039_; lean_object* v_toBind_1040_; lean_object* v_toPure_1041_; lean_object* v___x_1042_; lean_object* v___f_1043_; lean_object* v___f_1044_; lean_object* v___f_1045_; lean_object* v___x_1046_; 
v_toApplicative_1039_ = lean_ctor_get(v_inst_1033_, 0);
lean_inc_ref(v_toApplicative_1039_);
v_toBind_1040_ = lean_ctor_get(v_inst_1033_, 1);
lean_inc_n(v_toBind_1040_, 2);
lean_dec_ref(v_inst_1033_);
v_toPure_1041_ = lean_ctor_get(v_toApplicative_1039_, 1);
lean_inc_n(v_toPure_1041_, 2);
lean_dec_ref(v_toApplicative_1039_);
v___x_1042_ = lean_box(0);
v___f_1043_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1043_, 0, v_toBind_1040_);
v___f_1044_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1044_, 0, v_toPure_1041_);
v___f_1045_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1045_, 0, v___x_1042_);
lean_closure_set(v___f_1045_, 1, v_toPure_1041_);
lean_closure_set(v___f_1045_, 2, v_toBind_1040_);
lean_closure_set(v___f_1045_, 3, v___f_1044_);
v___x_1046_ = lean_apply_6(v_inst_1038_, v___f_1043_, lean_box(0), lean_box(0), v_it_1037_, v___x_1042_, v___f_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain___boxed(lean_object* v_00_u03b1_1047_, lean_object* v_m_1048_, lean_object* v_inst_1049_, lean_object* v_00_u03b2_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_, lean_object* v_it_1053_, lean_object* v_inst_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Std_IterM_Total_drain(v_00_u03b1_1047_, v_m_1048_, v_inst_1049_, v_00_u03b2_1050_, v_inst_1051_, v_inst_1052_, v_it_1053_, v_inst_1054_);
lean_dec(v_inst_1051_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__1(lean_object* v_toPure_1056_, lean_object* v_____do__lift_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_apply_2(v_toPure_1056_, lean_box(0), v_____do__lift_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__0(uint8_t v___x_1059_, lean_object* v_toPure_1060_, uint8_t v_____do__lift_1061_){
_start:
{
if (v_____do__lift_1061_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = lean_box(v___x_1059_);
v___x_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
v___x_1064_ = lean_apply_2(v_toPure_1060_, lean_box(0), v___x_1063_);
return v___x_1064_;
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = lean_box(v_____do__lift_1061_);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
v___x_1067_ = lean_apply_2(v_toPure_1060_, lean_box(0), v___x_1066_);
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__0___boxed(lean_object* v___x_1068_, lean_object* v_toPure_1069_, lean_object* v_____do__lift_1070_){
_start:
{
uint8_t v___x_155__boxed_1071_; uint8_t v_____do__lift_156__boxed_1072_; lean_object* v_res_1073_; 
v___x_155__boxed_1071_ = lean_unbox(v___x_1068_);
v_____do__lift_156__boxed_1072_ = lean_unbox(v_____do__lift_1070_);
v_res_1073_ = l_Std_IterM_anyM___redArg___lam__0(v___x_155__boxed_1071_, v_toPure_1069_, v_____do__lift_156__boxed_1072_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__2(lean_object* v_p_1074_, lean_object* v_toBind_1075_, lean_object* v___f_1076_, lean_object* v___f_1077_, lean_object* v_x1_1078_, lean_object* v_x2_1079_, uint8_t v_x3_1080_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = lean_apply_1(v_p_1074_, v_x1_1078_);
lean_inc(v_toBind_1075_);
v___x_1082_ = lean_apply_4(v_toBind_1075_, lean_box(0), lean_box(0), v___x_1081_, v___f_1076_);
v___x_1083_ = lean_apply_4(v_toBind_1075_, lean_box(0), lean_box(0), v___x_1082_, v___f_1077_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__2___boxed(lean_object* v_p_1084_, lean_object* v_toBind_1085_, lean_object* v___f_1086_, lean_object* v___f_1087_, lean_object* v_x1_1088_, lean_object* v_x2_1089_, lean_object* v_x3_1090_){
_start:
{
uint8_t v_x3_177__boxed_1091_; lean_object* v_res_1092_; 
v_x3_177__boxed_1091_ = lean_unbox(v_x3_1090_);
v_res_1092_ = l_Std_IterM_anyM___redArg___lam__2(v_p_1084_, v_toBind_1085_, v___f_1086_, v___f_1087_, v_x1_1088_, v_x2_1089_, v_x3_177__boxed_1091_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg(lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_p_1095_, lean_object* v_it_1096_){
_start:
{
lean_object* v_toApplicative_1097_; lean_object* v_toBind_1098_; lean_object* v_toPure_1099_; lean_object* v___f_1100_; lean_object* v___f_1101_; uint8_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___f_1104_; lean_object* v___f_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_toApplicative_1097_ = lean_ctor_get(v_inst_1093_, 0);
lean_inc_ref(v_toApplicative_1097_);
v_toBind_1098_ = lean_ctor_get(v_inst_1093_, 1);
lean_inc_n(v_toBind_1098_, 2);
lean_dec_ref(v_inst_1093_);
v_toPure_1099_ = lean_ctor_get(v_toApplicative_1097_, 1);
lean_inc_n(v_toPure_1099_, 2);
lean_dec_ref(v_toApplicative_1097_);
v___f_1100_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1100_, 0, v_toBind_1098_);
v___f_1101_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1101_, 0, v_toPure_1099_);
v___x_1102_ = 0;
v___x_1103_ = lean_box(v___x_1102_);
v___f_1104_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1104_, 0, v___x_1103_);
lean_closure_set(v___f_1104_, 1, v_toPure_1099_);
v___f_1105_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1105_, 0, v_p_1095_);
lean_closure_set(v___f_1105_, 1, v_toBind_1098_);
lean_closure_set(v___f_1105_, 2, v___f_1104_);
lean_closure_set(v___f_1105_, 3, v___f_1101_);
v___x_1106_ = lean_box(v___x_1102_);
v___x_1107_ = lean_apply_6(v_inst_1094_, v___f_1100_, lean_box(0), lean_box(0), v_it_1096_, v___x_1106_, v___f_1105_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM(lean_object* v_00_u03b1_1108_, lean_object* v_00_u03b2_1109_, lean_object* v_m_1110_, lean_object* v_inst_1111_, lean_object* v_inst_1112_, lean_object* v_inst_1113_, lean_object* v_p_1114_, lean_object* v_it_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Std_IterM_anyM___redArg(v_inst_1111_, v_inst_1113_, v_p_1114_, v_it_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___boxed(lean_object* v_00_u03b1_1117_, lean_object* v_00_u03b2_1118_, lean_object* v_m_1119_, lean_object* v_inst_1120_, lean_object* v_inst_1121_, lean_object* v_inst_1122_, lean_object* v_p_1123_, lean_object* v_it_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Std_IterM_anyM(v_00_u03b1_1117_, v_00_u03b2_1118_, v_m_1119_, v_inst_1120_, v_inst_1121_, v_inst_1122_, v_p_1123_, v_it_1124_);
lean_dec(v_inst_1121_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM___redArg(lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_p_1128_, lean_object* v_it_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Std_IterM_anyM___redArg(v_inst_1126_, v_inst_1127_, v_p_1128_, v_it_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM(lean_object* v_00_u03b1_1131_, lean_object* v_00_u03b2_1132_, lean_object* v_m_1133_, lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_inst_1136_, lean_object* v_p_1137_, lean_object* v_it_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Std_IterM_anyM___redArg(v_inst_1134_, v_inst_1136_, v_p_1137_, v_it_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM___boxed(lean_object* v_00_u03b1_1140_, lean_object* v_00_u03b2_1141_, lean_object* v_m_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_p_1146_, lean_object* v_it_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Std_IterM_Partial_anyM(v_00_u03b1_1140_, v_00_u03b2_1141_, v_m_1142_, v_inst_1143_, v_inst_1144_, v_inst_1145_, v_p_1146_, v_it_1147_);
lean_dec(v_inst_1144_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM___redArg(lean_object* v_inst_1149_, lean_object* v_inst_1150_, lean_object* v_p_1151_, lean_object* v_it_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Std_IterM_anyM___redArg(v_inst_1149_, v_inst_1150_, v_p_1151_, v_it_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM(lean_object* v_00_u03b1_1154_, lean_object* v_00_u03b2_1155_, lean_object* v_m_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_p_1161_, lean_object* v_it_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Std_IterM_anyM___redArg(v_inst_1157_, v_inst_1159_, v_p_1161_, v_it_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM___boxed(lean_object* v_00_u03b1_1164_, lean_object* v_00_u03b2_1165_, lean_object* v_m_1166_, lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_inst_1170_, lean_object* v_p_1171_, lean_object* v_it_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Std_IterM_Total_anyM(v_00_u03b1_1164_, v_00_u03b2_1165_, v_m_1166_, v_inst_1167_, v_inst_1168_, v_inst_1169_, v_inst_1170_, v_p_1171_, v_it_1172_);
lean_dec(v_inst_1168_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any___redArg___lam__0(lean_object* v_p_1174_, lean_object* v_toPure_1175_, lean_object* v_x_1176_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_apply_1(v_p_1174_, v_x_1176_);
v___x_1178_ = lean_apply_2(v_toPure_1175_, lean_box(0), v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any___redArg(lean_object* v_inst_1179_, lean_object* v_inst_1180_, lean_object* v_p_1181_, lean_object* v_it_1182_){
_start:
{
lean_object* v_toApplicative_1183_; lean_object* v_toPure_1184_; lean_object* v___f_1185_; lean_object* v___x_1186_; 
v_toApplicative_1183_ = lean_ctor_get(v_inst_1179_, 0);
v_toPure_1184_ = lean_ctor_get(v_toApplicative_1183_, 1);
lean_inc(v_toPure_1184_);
v___f_1185_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1185_, 0, v_p_1181_);
lean_closure_set(v___f_1185_, 1, v_toPure_1184_);
v___x_1186_ = l_Std_IterM_anyM___redArg(v_inst_1179_, v_inst_1180_, v___f_1185_, v_it_1182_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any(lean_object* v_00_u03b1_1187_, lean_object* v_00_u03b2_1188_, lean_object* v_m_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_p_1193_, lean_object* v_it_1194_){
_start:
{
lean_object* v_toApplicative_1195_; lean_object* v_toPure_1196_; lean_object* v___f_1197_; lean_object* v___x_1198_; 
v_toApplicative_1195_ = lean_ctor_get(v_inst_1190_, 0);
v_toPure_1196_ = lean_ctor_get(v_toApplicative_1195_, 1);
lean_inc(v_toPure_1196_);
v___f_1197_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1197_, 0, v_p_1193_);
lean_closure_set(v___f_1197_, 1, v_toPure_1196_);
v___x_1198_ = l_Std_IterM_anyM___redArg(v_inst_1190_, v_inst_1192_, v___f_1197_, v_it_1194_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any___boxed(lean_object* v_00_u03b1_1199_, lean_object* v_00_u03b2_1200_, lean_object* v_m_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_p_1205_, lean_object* v_it_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Std_IterM_any(v_00_u03b1_1199_, v_00_u03b2_1200_, v_m_1201_, v_inst_1202_, v_inst_1203_, v_inst_1204_, v_p_1205_, v_it_1206_);
lean_dec(v_inst_1203_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any___redArg(lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_p_1210_, lean_object* v_it_1211_){
_start:
{
lean_object* v_toApplicative_1212_; lean_object* v_toPure_1213_; lean_object* v___f_1214_; lean_object* v___x_1215_; 
v_toApplicative_1212_ = lean_ctor_get(v_inst_1208_, 0);
v_toPure_1213_ = lean_ctor_get(v_toApplicative_1212_, 1);
lean_inc(v_toPure_1213_);
v___f_1214_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1214_, 0, v_p_1210_);
lean_closure_set(v___f_1214_, 1, v_toPure_1213_);
v___x_1215_ = l_Std_IterM_anyM___redArg(v_inst_1208_, v_inst_1209_, v___f_1214_, v_it_1211_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any(lean_object* v_00_u03b1_1216_, lean_object* v_00_u03b2_1217_, lean_object* v_m_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_p_1222_, lean_object* v_it_1223_){
_start:
{
lean_object* v_toApplicative_1224_; lean_object* v_toPure_1225_; lean_object* v___f_1226_; lean_object* v___x_1227_; 
v_toApplicative_1224_ = lean_ctor_get(v_inst_1219_, 0);
v_toPure_1225_ = lean_ctor_get(v_toApplicative_1224_, 1);
lean_inc(v_toPure_1225_);
v___f_1226_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1226_, 0, v_p_1222_);
lean_closure_set(v___f_1226_, 1, v_toPure_1225_);
v___x_1227_ = l_Std_IterM_anyM___redArg(v_inst_1219_, v_inst_1221_, v___f_1226_, v_it_1223_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any___boxed(lean_object* v_00_u03b1_1228_, lean_object* v_00_u03b2_1229_, lean_object* v_m_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_p_1234_, lean_object* v_it_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Std_IterM_Partial_any(v_00_u03b1_1228_, v_00_u03b2_1229_, v_m_1230_, v_inst_1231_, v_inst_1232_, v_inst_1233_, v_p_1234_, v_it_1235_);
lean_dec(v_inst_1232_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_any___redArg(lean_object* v_inst_1237_, lean_object* v_inst_1238_, lean_object* v_p_1239_, lean_object* v_it_1240_){
_start:
{
lean_object* v_toApplicative_1241_; lean_object* v_toPure_1242_; lean_object* v___f_1243_; lean_object* v___x_1244_; 
v_toApplicative_1241_ = lean_ctor_get(v_inst_1237_, 0);
v_toPure_1242_ = lean_ctor_get(v_toApplicative_1241_, 1);
lean_inc(v_toPure_1242_);
v___f_1243_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1243_, 0, v_p_1239_);
lean_closure_set(v___f_1243_, 1, v_toPure_1242_);
v___x_1244_ = l_Std_IterM_anyM___redArg(v_inst_1237_, v_inst_1238_, v___f_1243_, v_it_1240_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_any(lean_object* v_00_u03b1_1245_, lean_object* v_00_u03b2_1246_, lean_object* v_m_1247_, lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_p_1252_, lean_object* v_it_1253_){
_start:
{
lean_object* v_toApplicative_1254_; lean_object* v_toPure_1255_; lean_object* v___f_1256_; lean_object* v___x_1257_; 
v_toApplicative_1254_ = lean_ctor_get(v_inst_1248_, 0);
v_toPure_1255_ = lean_ctor_get(v_toApplicative_1254_, 1);
lean_inc(v_toPure_1255_);
v___f_1256_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1256_, 0, v_p_1252_);
lean_closure_set(v___f_1256_, 1, v_toPure_1255_);
v___x_1257_ = l_Std_IterM_anyM___redArg(v_inst_1248_, v_inst_1250_, v___f_1256_, v_it_1253_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_any___boxed(lean_object* v_00_u03b1_1258_, lean_object* v_00_u03b2_1259_, lean_object* v_m_1260_, lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_p_1265_, lean_object* v_it_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Std_IterM_Total_any(v_00_u03b1_1258_, v_00_u03b2_1259_, v_m_1260_, v_inst_1261_, v_inst_1262_, v_inst_1263_, v_inst_1264_, v_p_1265_, v_it_1266_);
lean_dec(v_inst_1262_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg___lam__2(lean_object* v_toPure_1268_, uint8_t v___x_1269_, uint8_t v_____do__lift_1270_){
_start:
{
if (v_____do__lift_1270_ == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_box(v_____do__lift_1270_);
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
v___x_1273_ = lean_apply_2(v_toPure_1268_, lean_box(0), v___x_1272_);
return v___x_1273_;
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = lean_box(v___x_1269_);
v___x_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
v___x_1276_ = lean_apply_2(v_toPure_1268_, lean_box(0), v___x_1275_);
return v___x_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg___lam__2___boxed(lean_object* v_toPure_1277_, lean_object* v___x_1278_, lean_object* v_____do__lift_1279_){
_start:
{
uint8_t v___x_149__boxed_1280_; uint8_t v_____do__lift_150__boxed_1281_; lean_object* v_res_1282_; 
v___x_149__boxed_1280_ = lean_unbox(v___x_1278_);
v_____do__lift_150__boxed_1281_ = lean_unbox(v_____do__lift_1279_);
v_res_1282_ = l_Std_IterM_allM___redArg___lam__2(v_toPure_1277_, v___x_149__boxed_1280_, v_____do__lift_150__boxed_1281_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg(lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_p_1285_, lean_object* v_it_1286_){
_start:
{
lean_object* v_toApplicative_1287_; lean_object* v_toBind_1288_; lean_object* v_toPure_1289_; lean_object* v___f_1290_; lean_object* v___f_1291_; uint8_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___f_1294_; lean_object* v___f_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_toApplicative_1287_ = lean_ctor_get(v_inst_1283_, 0);
lean_inc_ref(v_toApplicative_1287_);
v_toBind_1288_ = lean_ctor_get(v_inst_1283_, 1);
lean_inc_n(v_toBind_1288_, 2);
lean_dec_ref(v_inst_1283_);
v_toPure_1289_ = lean_ctor_get(v_toApplicative_1287_, 1);
lean_inc_n(v_toPure_1289_, 2);
lean_dec_ref(v_toApplicative_1287_);
v___f_1290_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1290_, 0, v_toBind_1288_);
v___f_1291_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1291_, 0, v_toPure_1289_);
v___x_1292_ = 1;
v___x_1293_ = lean_box(v___x_1292_);
v___f_1294_ = lean_alloc_closure((void*)(l_Std_IterM_allM___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1294_, 0, v_toPure_1289_);
lean_closure_set(v___f_1294_, 1, v___x_1293_);
v___f_1295_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1295_, 0, v_p_1285_);
lean_closure_set(v___f_1295_, 1, v_toBind_1288_);
lean_closure_set(v___f_1295_, 2, v___f_1294_);
lean_closure_set(v___f_1295_, 3, v___f_1291_);
v___x_1296_ = lean_box(v___x_1292_);
v___x_1297_ = lean_apply_6(v_inst_1284_, v___f_1290_, lean_box(0), lean_box(0), v_it_1286_, v___x_1296_, v___f_1295_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM(lean_object* v_00_u03b1_1298_, lean_object* v_00_u03b2_1299_, lean_object* v_m_1300_, lean_object* v_inst_1301_, lean_object* v_inst_1302_, lean_object* v_inst_1303_, lean_object* v_p_1304_, lean_object* v_it_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Std_IterM_allM___redArg(v_inst_1301_, v_inst_1303_, v_p_1304_, v_it_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM___boxed(lean_object* v_00_u03b1_1307_, lean_object* v_00_u03b2_1308_, lean_object* v_m_1309_, lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_inst_1312_, lean_object* v_p_1313_, lean_object* v_it_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Std_IterM_allM(v_00_u03b1_1307_, v_00_u03b2_1308_, v_m_1309_, v_inst_1310_, v_inst_1311_, v_inst_1312_, v_p_1313_, v_it_1314_);
lean_dec(v_inst_1311_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM___redArg(lean_object* v_inst_1316_, lean_object* v_inst_1317_, lean_object* v_p_1318_, lean_object* v_it_1319_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Std_IterM_allM___redArg(v_inst_1316_, v_inst_1317_, v_p_1318_, v_it_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM(lean_object* v_00_u03b1_1321_, lean_object* v_00_u03b2_1322_, lean_object* v_m_1323_, lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_p_1327_, lean_object* v_it_1328_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Std_IterM_allM___redArg(v_inst_1324_, v_inst_1326_, v_p_1327_, v_it_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM___boxed(lean_object* v_00_u03b1_1330_, lean_object* v_00_u03b2_1331_, lean_object* v_m_1332_, lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_p_1336_, lean_object* v_it_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Std_IterM_Partial_allM(v_00_u03b1_1330_, v_00_u03b2_1331_, v_m_1332_, v_inst_1333_, v_inst_1334_, v_inst_1335_, v_p_1336_, v_it_1337_);
lean_dec(v_inst_1334_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM___redArg(lean_object* v_inst_1339_, lean_object* v_inst_1340_, lean_object* v_p_1341_, lean_object* v_it_1342_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Std_IterM_allM___redArg(v_inst_1339_, v_inst_1340_, v_p_1341_, v_it_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM(lean_object* v_00_u03b1_1344_, lean_object* v_00_u03b2_1345_, lean_object* v_m_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_inst_1350_, lean_object* v_p_1351_, lean_object* v_it_1352_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Std_IterM_allM___redArg(v_inst_1347_, v_inst_1349_, v_p_1351_, v_it_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM___boxed(lean_object* v_00_u03b1_1354_, lean_object* v_00_u03b2_1355_, lean_object* v_m_1356_, lean_object* v_inst_1357_, lean_object* v_inst_1358_, lean_object* v_inst_1359_, lean_object* v_inst_1360_, lean_object* v_p_1361_, lean_object* v_it_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Std_IterM_Total_allM(v_00_u03b1_1354_, v_00_u03b2_1355_, v_m_1356_, v_inst_1357_, v_inst_1358_, v_inst_1359_, v_inst_1360_, v_p_1361_, v_it_1362_);
lean_dec(v_inst_1358_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_all___redArg(lean_object* v_inst_1364_, lean_object* v_inst_1365_, lean_object* v_p_1366_, lean_object* v_it_1367_){
_start:
{
lean_object* v_toApplicative_1368_; lean_object* v_toPure_1369_; lean_object* v___f_1370_; lean_object* v___x_1371_; 
v_toApplicative_1368_ = lean_ctor_get(v_inst_1364_, 0);
v_toPure_1369_ = lean_ctor_get(v_toApplicative_1368_, 1);
lean_inc(v_toPure_1369_);
v___f_1370_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1370_, 0, v_p_1366_);
lean_closure_set(v___f_1370_, 1, v_toPure_1369_);
v___x_1371_ = l_Std_IterM_allM___redArg(v_inst_1364_, v_inst_1365_, v___f_1370_, v_it_1367_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_all(lean_object* v_00_u03b1_1372_, lean_object* v_00_u03b2_1373_, lean_object* v_m_1374_, lean_object* v_inst_1375_, lean_object* v_inst_1376_, lean_object* v_inst_1377_, lean_object* v_p_1378_, lean_object* v_it_1379_){
_start:
{
lean_object* v_toApplicative_1380_; lean_object* v_toPure_1381_; lean_object* v___f_1382_; lean_object* v___x_1383_; 
v_toApplicative_1380_ = lean_ctor_get(v_inst_1375_, 0);
v_toPure_1381_ = lean_ctor_get(v_toApplicative_1380_, 1);
lean_inc(v_toPure_1381_);
v___f_1382_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1382_, 0, v_p_1378_);
lean_closure_set(v___f_1382_, 1, v_toPure_1381_);
v___x_1383_ = l_Std_IterM_allM___redArg(v_inst_1375_, v_inst_1377_, v___f_1382_, v_it_1379_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_all___boxed(lean_object* v_00_u03b1_1384_, lean_object* v_00_u03b2_1385_, lean_object* v_m_1386_, lean_object* v_inst_1387_, lean_object* v_inst_1388_, lean_object* v_inst_1389_, lean_object* v_p_1390_, lean_object* v_it_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Std_IterM_all(v_00_u03b1_1384_, v_00_u03b2_1385_, v_m_1386_, v_inst_1387_, v_inst_1388_, v_inst_1389_, v_p_1390_, v_it_1391_);
lean_dec(v_inst_1388_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all___redArg(lean_object* v_inst_1393_, lean_object* v_inst_1394_, lean_object* v_p_1395_, lean_object* v_it_1396_){
_start:
{
lean_object* v_toApplicative_1397_; lean_object* v_toPure_1398_; lean_object* v___f_1399_; lean_object* v___x_1400_; 
v_toApplicative_1397_ = lean_ctor_get(v_inst_1393_, 0);
v_toPure_1398_ = lean_ctor_get(v_toApplicative_1397_, 1);
lean_inc(v_toPure_1398_);
v___f_1399_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1399_, 0, v_p_1395_);
lean_closure_set(v___f_1399_, 1, v_toPure_1398_);
v___x_1400_ = l_Std_IterM_allM___redArg(v_inst_1393_, v_inst_1394_, v___f_1399_, v_it_1396_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all(lean_object* v_00_u03b1_1401_, lean_object* v_00_u03b2_1402_, lean_object* v_m_1403_, lean_object* v_inst_1404_, lean_object* v_inst_1405_, lean_object* v_inst_1406_, lean_object* v_p_1407_, lean_object* v_it_1408_){
_start:
{
lean_object* v_toApplicative_1409_; lean_object* v_toPure_1410_; lean_object* v___f_1411_; lean_object* v___x_1412_; 
v_toApplicative_1409_ = lean_ctor_get(v_inst_1404_, 0);
v_toPure_1410_ = lean_ctor_get(v_toApplicative_1409_, 1);
lean_inc(v_toPure_1410_);
v___f_1411_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1411_, 0, v_p_1407_);
lean_closure_set(v___f_1411_, 1, v_toPure_1410_);
v___x_1412_ = l_Std_IterM_allM___redArg(v_inst_1404_, v_inst_1406_, v___f_1411_, v_it_1408_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all___boxed(lean_object* v_00_u03b1_1413_, lean_object* v_00_u03b2_1414_, lean_object* v_m_1415_, lean_object* v_inst_1416_, lean_object* v_inst_1417_, lean_object* v_inst_1418_, lean_object* v_p_1419_, lean_object* v_it_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Std_IterM_Partial_all(v_00_u03b1_1413_, v_00_u03b2_1414_, v_m_1415_, v_inst_1416_, v_inst_1417_, v_inst_1418_, v_p_1419_, v_it_1420_);
lean_dec(v_inst_1417_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_all___redArg(lean_object* v_inst_1422_, lean_object* v_inst_1423_, lean_object* v_p_1424_, lean_object* v_it_1425_){
_start:
{
lean_object* v_toApplicative_1426_; lean_object* v_toPure_1427_; lean_object* v___f_1428_; lean_object* v___x_1429_; 
v_toApplicative_1426_ = lean_ctor_get(v_inst_1422_, 0);
v_toPure_1427_ = lean_ctor_get(v_toApplicative_1426_, 1);
lean_inc(v_toPure_1427_);
v___f_1428_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1428_, 0, v_p_1424_);
lean_closure_set(v___f_1428_, 1, v_toPure_1427_);
v___x_1429_ = l_Std_IterM_allM___redArg(v_inst_1422_, v_inst_1423_, v___f_1428_, v_it_1425_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_all(lean_object* v_00_u03b1_1430_, lean_object* v_00_u03b2_1431_, lean_object* v_m_1432_, lean_object* v_inst_1433_, lean_object* v_inst_1434_, lean_object* v_inst_1435_, lean_object* v_inst_1436_, lean_object* v_p_1437_, lean_object* v_it_1438_){
_start:
{
lean_object* v_toApplicative_1439_; lean_object* v_toPure_1440_; lean_object* v___f_1441_; lean_object* v___x_1442_; 
v_toApplicative_1439_ = lean_ctor_get(v_inst_1433_, 0);
v_toPure_1440_ = lean_ctor_get(v_toApplicative_1439_, 1);
lean_inc(v_toPure_1440_);
v___f_1441_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1441_, 0, v_p_1437_);
lean_closure_set(v___f_1441_, 1, v_toPure_1440_);
v___x_1442_ = l_Std_IterM_allM___redArg(v_inst_1433_, v_inst_1435_, v___f_1441_, v_it_1438_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_all___boxed(lean_object* v_00_u03b1_1443_, lean_object* v_00_u03b2_1444_, lean_object* v_m_1445_, lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v_inst_1448_, lean_object* v_inst_1449_, lean_object* v_p_1450_, lean_object* v_it_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Std_IterM_Total_all(v_00_u03b1_1443_, v_00_u03b2_1444_, v_m_1445_, v_inst_1446_, v_inst_1447_, v_inst_1448_, v_inst_1449_, v_p_1450_, v_it_1451_);
lean_dec(v_inst_1447_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__1(lean_object* v_toPure_1453_, lean_object* v_____do__lift_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_apply_2(v_toPure_1453_, lean_box(0), v_____do__lift_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__0(lean_object* v___x_1456_, lean_object* v_toPure_1457_, lean_object* v_____do__lift_1458_){
_start:
{
if (lean_obj_tag(v_____do__lift_1458_) == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1456_);
v___x_1460_ = lean_apply_2(v_toPure_1457_, lean_box(0), v___x_1459_);
return v___x_1460_;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec(v___x_1456_);
v___x_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1461_, 0, v_____do__lift_1458_);
v___x_1462_ = lean_apply_2(v_toPure_1457_, lean_box(0), v___x_1461_);
return v___x_1462_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__2(lean_object* v_f_1463_, lean_object* v_toBind_1464_, lean_object* v___f_1465_, lean_object* v___f_1466_, lean_object* v_x1_1467_, lean_object* v_x2_1468_, lean_object* v_x3_1469_){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1470_ = lean_apply_1(v_f_1463_, v_x1_1467_);
lean_inc(v_toBind_1464_);
v___x_1471_ = lean_apply_4(v_toBind_1464_, lean_box(0), lean_box(0), v___x_1470_, v___f_1465_);
v___x_1472_ = lean_apply_4(v_toBind_1464_, lean_box(0), lean_box(0), v___x_1471_, v___f_1466_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed(lean_object* v_f_1473_, lean_object* v_toBind_1474_, lean_object* v___f_1475_, lean_object* v___f_1476_, lean_object* v_x1_1477_, lean_object* v_x2_1478_, lean_object* v_x3_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Std_IterM_findSomeM_x3f___redArg___lam__2(v_f_1473_, v_toBind_1474_, v___f_1475_, v___f_1476_, v_x1_1477_, v_x2_1478_, v_x3_1479_);
lean_dec(v_x3_1479_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg(lean_object* v_inst_1481_, lean_object* v_inst_1482_, lean_object* v_it_1483_, lean_object* v_f_1484_){
_start:
{
lean_object* v_toApplicative_1485_; lean_object* v_toBind_1486_; lean_object* v_toPure_1487_; lean_object* v___f_1488_; lean_object* v___f_1489_; lean_object* v___x_1490_; lean_object* v___f_1491_; lean_object* v___f_1492_; lean_object* v___x_1493_; 
v_toApplicative_1485_ = lean_ctor_get(v_inst_1481_, 0);
lean_inc_ref(v_toApplicative_1485_);
v_toBind_1486_ = lean_ctor_get(v_inst_1481_, 1);
lean_inc_n(v_toBind_1486_, 2);
lean_dec_ref(v_inst_1481_);
v_toPure_1487_ = lean_ctor_get(v_toApplicative_1485_, 1);
lean_inc_n(v_toPure_1487_, 2);
lean_dec_ref(v_toApplicative_1485_);
v___f_1488_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1488_, 0, v_toBind_1486_);
v___f_1489_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1489_, 0, v_toPure_1487_);
v___x_1490_ = lean_box(0);
v___f_1491_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1491_, 0, v___x_1490_);
lean_closure_set(v___f_1491_, 1, v_toPure_1487_);
v___f_1492_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1492_, 0, v_f_1484_);
lean_closure_set(v___f_1492_, 1, v_toBind_1486_);
lean_closure_set(v___f_1492_, 2, v___f_1491_);
lean_closure_set(v___f_1492_, 3, v___f_1489_);
v___x_1493_ = lean_apply_6(v_inst_1482_, v___f_1488_, lean_box(0), lean_box(0), v_it_1483_, v___x_1490_, v___f_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f(lean_object* v_00_u03b1_1494_, lean_object* v_00_u03b2_1495_, lean_object* v_00_u03b3_1496_, lean_object* v_m_1497_, lean_object* v_inst_1498_, lean_object* v_inst_1499_, lean_object* v_inst_1500_, lean_object* v_it_1501_, lean_object* v_f_1502_){
_start:
{
lean_object* v_toApplicative_1503_; lean_object* v_toBind_1504_; lean_object* v_toPure_1505_; lean_object* v___f_1506_; lean_object* v___f_1507_; lean_object* v___x_1508_; lean_object* v___f_1509_; lean_object* v___f_1510_; lean_object* v___x_1511_; 
v_toApplicative_1503_ = lean_ctor_get(v_inst_1498_, 0);
lean_inc_ref(v_toApplicative_1503_);
v_toBind_1504_ = lean_ctor_get(v_inst_1498_, 1);
lean_inc_n(v_toBind_1504_, 2);
lean_dec_ref(v_inst_1498_);
v_toPure_1505_ = lean_ctor_get(v_toApplicative_1503_, 1);
lean_inc_n(v_toPure_1505_, 2);
lean_dec_ref(v_toApplicative_1503_);
v___f_1506_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1506_, 0, v_toBind_1504_);
v___f_1507_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1507_, 0, v_toPure_1505_);
v___x_1508_ = lean_box(0);
v___f_1509_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1509_, 0, v___x_1508_);
lean_closure_set(v___f_1509_, 1, v_toPure_1505_);
v___f_1510_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1510_, 0, v_f_1502_);
lean_closure_set(v___f_1510_, 1, v_toBind_1504_);
lean_closure_set(v___f_1510_, 2, v___f_1509_);
lean_closure_set(v___f_1510_, 3, v___f_1507_);
v___x_1511_ = lean_apply_6(v_inst_1500_, v___f_1506_, lean_box(0), lean_box(0), v_it_1501_, v___x_1508_, v___f_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___boxed(lean_object* v_00_u03b1_1512_, lean_object* v_00_u03b2_1513_, lean_object* v_00_u03b3_1514_, lean_object* v_m_1515_, lean_object* v_inst_1516_, lean_object* v_inst_1517_, lean_object* v_inst_1518_, lean_object* v_it_1519_, lean_object* v_f_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Std_IterM_findSomeM_x3f(v_00_u03b1_1512_, v_00_u03b2_1513_, v_00_u03b3_1514_, v_m_1515_, v_inst_1516_, v_inst_1517_, v_inst_1518_, v_it_1519_, v_f_1520_);
lean_dec(v_inst_1517_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f___redArg(lean_object* v_inst_1522_, lean_object* v_inst_1523_, lean_object* v_it_1524_, lean_object* v_f_1525_){
_start:
{
lean_object* v_toApplicative_1526_; lean_object* v_toBind_1527_; lean_object* v_toPure_1528_; lean_object* v___f_1529_; lean_object* v___f_1530_; lean_object* v___x_1531_; lean_object* v___f_1532_; lean_object* v___f_1533_; lean_object* v___x_1534_; 
v_toApplicative_1526_ = lean_ctor_get(v_inst_1522_, 0);
lean_inc_ref(v_toApplicative_1526_);
v_toBind_1527_ = lean_ctor_get(v_inst_1522_, 1);
lean_inc_n(v_toBind_1527_, 2);
lean_dec_ref(v_inst_1522_);
v_toPure_1528_ = lean_ctor_get(v_toApplicative_1526_, 1);
lean_inc_n(v_toPure_1528_, 2);
lean_dec_ref(v_toApplicative_1526_);
v___f_1529_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1529_, 0, v_toBind_1527_);
v___f_1530_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1530_, 0, v_toPure_1528_);
v___x_1531_ = lean_box(0);
v___f_1532_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1532_, 0, v___x_1531_);
lean_closure_set(v___f_1532_, 1, v_toPure_1528_);
v___f_1533_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1533_, 0, v_f_1525_);
lean_closure_set(v___f_1533_, 1, v_toBind_1527_);
lean_closure_set(v___f_1533_, 2, v___f_1532_);
lean_closure_set(v___f_1533_, 3, v___f_1530_);
v___x_1534_ = lean_apply_6(v_inst_1523_, v___f_1529_, lean_box(0), lean_box(0), v_it_1524_, v___x_1531_, v___f_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f(lean_object* v_00_u03b1_1535_, lean_object* v_00_u03b2_1536_, lean_object* v_00_u03b3_1537_, lean_object* v_m_1538_, lean_object* v_inst_1539_, lean_object* v_inst_1540_, lean_object* v_inst_1541_, lean_object* v_it_1542_, lean_object* v_f_1543_){
_start:
{
lean_object* v_toApplicative_1544_; lean_object* v_toBind_1545_; lean_object* v_toPure_1546_; lean_object* v___f_1547_; lean_object* v___f_1548_; lean_object* v___x_1549_; lean_object* v___f_1550_; lean_object* v___f_1551_; lean_object* v___x_1552_; 
v_toApplicative_1544_ = lean_ctor_get(v_inst_1539_, 0);
lean_inc_ref(v_toApplicative_1544_);
v_toBind_1545_ = lean_ctor_get(v_inst_1539_, 1);
lean_inc_n(v_toBind_1545_, 2);
lean_dec_ref(v_inst_1539_);
v_toPure_1546_ = lean_ctor_get(v_toApplicative_1544_, 1);
lean_inc_n(v_toPure_1546_, 2);
lean_dec_ref(v_toApplicative_1544_);
v___f_1547_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1547_, 0, v_toBind_1545_);
v___f_1548_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1548_, 0, v_toPure_1546_);
v___x_1549_ = lean_box(0);
v___f_1550_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1550_, 0, v___x_1549_);
lean_closure_set(v___f_1550_, 1, v_toPure_1546_);
v___f_1551_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1551_, 0, v_f_1543_);
lean_closure_set(v___f_1551_, 1, v_toBind_1545_);
lean_closure_set(v___f_1551_, 2, v___f_1550_);
lean_closure_set(v___f_1551_, 3, v___f_1548_);
v___x_1552_ = lean_apply_6(v_inst_1541_, v___f_1547_, lean_box(0), lean_box(0), v_it_1542_, v___x_1549_, v___f_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f___boxed(lean_object* v_00_u03b1_1553_, lean_object* v_00_u03b2_1554_, lean_object* v_00_u03b3_1555_, lean_object* v_m_1556_, lean_object* v_inst_1557_, lean_object* v_inst_1558_, lean_object* v_inst_1559_, lean_object* v_it_1560_, lean_object* v_f_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Std_IterM_Partial_findSomeM_x3f(v_00_u03b1_1553_, v_00_u03b2_1554_, v_00_u03b3_1555_, v_m_1556_, v_inst_1557_, v_inst_1558_, v_inst_1559_, v_it_1560_, v_f_1561_);
lean_dec(v_inst_1558_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f___redArg(lean_object* v_inst_1563_, lean_object* v_inst_1564_, lean_object* v_it_1565_, lean_object* v_f_1566_){
_start:
{
lean_object* v_toApplicative_1567_; lean_object* v_toBind_1568_; lean_object* v_toPure_1569_; lean_object* v___f_1570_; lean_object* v___f_1571_; lean_object* v___x_1572_; lean_object* v___f_1573_; lean_object* v___f_1574_; lean_object* v___x_1575_; 
v_toApplicative_1567_ = lean_ctor_get(v_inst_1563_, 0);
lean_inc_ref(v_toApplicative_1567_);
v_toBind_1568_ = lean_ctor_get(v_inst_1563_, 1);
lean_inc_n(v_toBind_1568_, 2);
lean_dec_ref(v_inst_1563_);
v_toPure_1569_ = lean_ctor_get(v_toApplicative_1567_, 1);
lean_inc_n(v_toPure_1569_, 2);
lean_dec_ref(v_toApplicative_1567_);
v___f_1570_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1570_, 0, v_toBind_1568_);
v___f_1571_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1571_, 0, v_toPure_1569_);
v___x_1572_ = lean_box(0);
v___f_1573_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1573_, 0, v___x_1572_);
lean_closure_set(v___f_1573_, 1, v_toPure_1569_);
v___f_1574_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1574_, 0, v_f_1566_);
lean_closure_set(v___f_1574_, 1, v_toBind_1568_);
lean_closure_set(v___f_1574_, 2, v___f_1573_);
lean_closure_set(v___f_1574_, 3, v___f_1571_);
v___x_1575_ = lean_apply_6(v_inst_1564_, v___f_1570_, lean_box(0), lean_box(0), v_it_1565_, v___x_1572_, v___f_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f(lean_object* v_00_u03b1_1576_, lean_object* v_00_u03b2_1577_, lean_object* v_00_u03b3_1578_, lean_object* v_m_1579_, lean_object* v_inst_1580_, lean_object* v_inst_1581_, lean_object* v_inst_1582_, lean_object* v_inst_1583_, lean_object* v_it_1584_, lean_object* v_f_1585_){
_start:
{
lean_object* v_toApplicative_1586_; lean_object* v_toBind_1587_; lean_object* v_toPure_1588_; lean_object* v___f_1589_; lean_object* v___f_1590_; lean_object* v___x_1591_; lean_object* v___f_1592_; lean_object* v___f_1593_; lean_object* v___x_1594_; 
v_toApplicative_1586_ = lean_ctor_get(v_inst_1580_, 0);
lean_inc_ref(v_toApplicative_1586_);
v_toBind_1587_ = lean_ctor_get(v_inst_1580_, 1);
lean_inc_n(v_toBind_1587_, 2);
lean_dec_ref(v_inst_1580_);
v_toPure_1588_ = lean_ctor_get(v_toApplicative_1586_, 1);
lean_inc_n(v_toPure_1588_, 2);
lean_dec_ref(v_toApplicative_1586_);
v___f_1589_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1589_, 0, v_toBind_1587_);
v___f_1590_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1590_, 0, v_toPure_1588_);
v___x_1591_ = lean_box(0);
v___f_1592_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1592_, 0, v___x_1591_);
lean_closure_set(v___f_1592_, 1, v_toPure_1588_);
v___f_1593_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1593_, 0, v_f_1585_);
lean_closure_set(v___f_1593_, 1, v_toBind_1587_);
lean_closure_set(v___f_1593_, 2, v___f_1592_);
lean_closure_set(v___f_1593_, 3, v___f_1590_);
v___x_1594_ = lean_apply_6(v_inst_1582_, v___f_1589_, lean_box(0), lean_box(0), v_it_1584_, v___x_1591_, v___f_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f___boxed(lean_object* v_00_u03b1_1595_, lean_object* v_00_u03b2_1596_, lean_object* v_00_u03b3_1597_, lean_object* v_m_1598_, lean_object* v_inst_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_inst_1602_, lean_object* v_it_1603_, lean_object* v_f_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Std_IterM_Total_findSomeM_x3f(v_00_u03b1_1595_, v_00_u03b2_1596_, v_00_u03b3_1597_, v_m_1598_, v_inst_1599_, v_inst_1600_, v_inst_1601_, v_inst_1602_, v_it_1603_, v_f_1604_);
lean_dec(v_inst_1600_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg___lam__3(lean_object* v_f_1606_, lean_object* v_toPure_1607_, lean_object* v_toBind_1608_, lean_object* v___f_1609_, lean_object* v___f_1610_, lean_object* v_x1_1611_, lean_object* v_x2_1612_, lean_object* v_x3_1613_){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1614_ = lean_apply_1(v_f_1606_, v_x1_1611_);
v___x_1615_ = lean_apply_2(v_toPure_1607_, lean_box(0), v___x_1614_);
lean_inc(v_toBind_1608_);
v___x_1616_ = lean_apply_4(v_toBind_1608_, lean_box(0), lean_box(0), v___x_1615_, v___f_1609_);
v___x_1617_ = lean_apply_4(v_toBind_1608_, lean_box(0), lean_box(0), v___x_1616_, v___f_1610_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg___lam__3___boxed(lean_object* v_f_1618_, lean_object* v_toPure_1619_, lean_object* v_toBind_1620_, lean_object* v___f_1621_, lean_object* v___f_1622_, lean_object* v_x1_1623_, lean_object* v_x2_1624_, lean_object* v_x3_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Std_IterM_findSome_x3f___redArg___lam__3(v_f_1618_, v_toPure_1619_, v_toBind_1620_, v___f_1621_, v___f_1622_, v_x1_1623_, v_x2_1624_, v_x3_1625_);
lean_dec(v_x3_1625_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg(lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_it_1629_, lean_object* v_f_1630_){
_start:
{
lean_object* v_toApplicative_1631_; lean_object* v_toBind_1632_; lean_object* v_toPure_1633_; lean_object* v___f_1634_; lean_object* v___f_1635_; lean_object* v___x_1636_; lean_object* v___f_1637_; lean_object* v___f_1638_; lean_object* v___x_1639_; 
v_toApplicative_1631_ = lean_ctor_get(v_inst_1627_, 0);
lean_inc_ref(v_toApplicative_1631_);
v_toBind_1632_ = lean_ctor_get(v_inst_1627_, 1);
lean_inc_n(v_toBind_1632_, 2);
lean_dec_ref(v_inst_1627_);
v_toPure_1633_ = lean_ctor_get(v_toApplicative_1631_, 1);
lean_inc_n(v_toPure_1633_, 3);
lean_dec_ref(v_toApplicative_1631_);
v___f_1634_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1634_, 0, v_toBind_1632_);
v___f_1635_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1635_, 0, v_toPure_1633_);
v___x_1636_ = lean_box(0);
v___f_1637_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1637_, 0, v___x_1636_);
lean_closure_set(v___f_1637_, 1, v_toPure_1633_);
v___f_1638_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1638_, 0, v_f_1630_);
lean_closure_set(v___f_1638_, 1, v_toPure_1633_);
lean_closure_set(v___f_1638_, 2, v_toBind_1632_);
lean_closure_set(v___f_1638_, 3, v___f_1637_);
lean_closure_set(v___f_1638_, 4, v___f_1635_);
v___x_1639_ = lean_apply_6(v_inst_1628_, v___f_1634_, lean_box(0), lean_box(0), v_it_1629_, v___x_1636_, v___f_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f(lean_object* v_00_u03b1_1640_, lean_object* v_00_u03b2_1641_, lean_object* v_00_u03b3_1642_, lean_object* v_m_1643_, lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_inst_1646_, lean_object* v_it_1647_, lean_object* v_f_1648_){
_start:
{
lean_object* v_toApplicative_1649_; lean_object* v_toBind_1650_; lean_object* v_toPure_1651_; lean_object* v___f_1652_; lean_object* v___f_1653_; lean_object* v___x_1654_; lean_object* v___f_1655_; lean_object* v___f_1656_; lean_object* v___x_1657_; 
v_toApplicative_1649_ = lean_ctor_get(v_inst_1644_, 0);
lean_inc_ref(v_toApplicative_1649_);
v_toBind_1650_ = lean_ctor_get(v_inst_1644_, 1);
lean_inc_n(v_toBind_1650_, 2);
lean_dec_ref(v_inst_1644_);
v_toPure_1651_ = lean_ctor_get(v_toApplicative_1649_, 1);
lean_inc_n(v_toPure_1651_, 3);
lean_dec_ref(v_toApplicative_1649_);
v___f_1652_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1652_, 0, v_toBind_1650_);
v___f_1653_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1653_, 0, v_toPure_1651_);
v___x_1654_ = lean_box(0);
v___f_1655_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1655_, 0, v___x_1654_);
lean_closure_set(v___f_1655_, 1, v_toPure_1651_);
v___f_1656_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1656_, 0, v_f_1648_);
lean_closure_set(v___f_1656_, 1, v_toPure_1651_);
lean_closure_set(v___f_1656_, 2, v_toBind_1650_);
lean_closure_set(v___f_1656_, 3, v___f_1655_);
lean_closure_set(v___f_1656_, 4, v___f_1653_);
v___x_1657_ = lean_apply_6(v_inst_1646_, v___f_1652_, lean_box(0), lean_box(0), v_it_1647_, v___x_1654_, v___f_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___boxed(lean_object* v_00_u03b1_1658_, lean_object* v_00_u03b2_1659_, lean_object* v_00_u03b3_1660_, lean_object* v_m_1661_, lean_object* v_inst_1662_, lean_object* v_inst_1663_, lean_object* v_inst_1664_, lean_object* v_it_1665_, lean_object* v_f_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Std_IterM_findSome_x3f(v_00_u03b1_1658_, v_00_u03b2_1659_, v_00_u03b3_1660_, v_m_1661_, v_inst_1662_, v_inst_1663_, v_inst_1664_, v_it_1665_, v_f_1666_);
lean_dec(v_inst_1663_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f___redArg(lean_object* v_inst_1668_, lean_object* v_inst_1669_, lean_object* v_it_1670_, lean_object* v_f_1671_){
_start:
{
lean_object* v_toApplicative_1672_; lean_object* v_toBind_1673_; lean_object* v_toPure_1674_; lean_object* v___f_1675_; lean_object* v___f_1676_; lean_object* v___x_1677_; lean_object* v___f_1678_; lean_object* v___f_1679_; lean_object* v___x_1680_; 
v_toApplicative_1672_ = lean_ctor_get(v_inst_1668_, 0);
lean_inc_ref(v_toApplicative_1672_);
v_toBind_1673_ = lean_ctor_get(v_inst_1668_, 1);
lean_inc_n(v_toBind_1673_, 2);
lean_dec_ref(v_inst_1668_);
v_toPure_1674_ = lean_ctor_get(v_toApplicative_1672_, 1);
lean_inc_n(v_toPure_1674_, 3);
lean_dec_ref(v_toApplicative_1672_);
v___f_1675_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1675_, 0, v_toBind_1673_);
v___f_1676_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1676_, 0, v_toPure_1674_);
v___x_1677_ = lean_box(0);
v___f_1678_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1678_, 0, v___x_1677_);
lean_closure_set(v___f_1678_, 1, v_toPure_1674_);
v___f_1679_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1679_, 0, v_f_1671_);
lean_closure_set(v___f_1679_, 1, v_toPure_1674_);
lean_closure_set(v___f_1679_, 2, v_toBind_1673_);
lean_closure_set(v___f_1679_, 3, v___f_1678_);
lean_closure_set(v___f_1679_, 4, v___f_1676_);
v___x_1680_ = lean_apply_6(v_inst_1669_, v___f_1675_, lean_box(0), lean_box(0), v_it_1670_, v___x_1677_, v___f_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f(lean_object* v_00_u03b1_1681_, lean_object* v_00_u03b2_1682_, lean_object* v_00_u03b3_1683_, lean_object* v_m_1684_, lean_object* v_inst_1685_, lean_object* v_inst_1686_, lean_object* v_inst_1687_, lean_object* v_it_1688_, lean_object* v_f_1689_){
_start:
{
lean_object* v_toApplicative_1690_; lean_object* v_toBind_1691_; lean_object* v_toPure_1692_; lean_object* v___f_1693_; lean_object* v___f_1694_; lean_object* v___x_1695_; lean_object* v___f_1696_; lean_object* v___f_1697_; lean_object* v___x_1698_; 
v_toApplicative_1690_ = lean_ctor_get(v_inst_1685_, 0);
lean_inc_ref(v_toApplicative_1690_);
v_toBind_1691_ = lean_ctor_get(v_inst_1685_, 1);
lean_inc_n(v_toBind_1691_, 2);
lean_dec_ref(v_inst_1685_);
v_toPure_1692_ = lean_ctor_get(v_toApplicative_1690_, 1);
lean_inc_n(v_toPure_1692_, 3);
lean_dec_ref(v_toApplicative_1690_);
v___f_1693_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1693_, 0, v_toBind_1691_);
v___f_1694_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1694_, 0, v_toPure_1692_);
v___x_1695_ = lean_box(0);
v___f_1696_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1696_, 0, v___x_1695_);
lean_closure_set(v___f_1696_, 1, v_toPure_1692_);
v___f_1697_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1697_, 0, v_f_1689_);
lean_closure_set(v___f_1697_, 1, v_toPure_1692_);
lean_closure_set(v___f_1697_, 2, v_toBind_1691_);
lean_closure_set(v___f_1697_, 3, v___f_1696_);
lean_closure_set(v___f_1697_, 4, v___f_1694_);
v___x_1698_ = lean_apply_6(v_inst_1687_, v___f_1693_, lean_box(0), lean_box(0), v_it_1688_, v___x_1695_, v___f_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f___boxed(lean_object* v_00_u03b1_1699_, lean_object* v_00_u03b2_1700_, lean_object* v_00_u03b3_1701_, lean_object* v_m_1702_, lean_object* v_inst_1703_, lean_object* v_inst_1704_, lean_object* v_inst_1705_, lean_object* v_it_1706_, lean_object* v_f_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Std_IterM_Partial_findSome_x3f(v_00_u03b1_1699_, v_00_u03b2_1700_, v_00_u03b3_1701_, v_m_1702_, v_inst_1703_, v_inst_1704_, v_inst_1705_, v_it_1706_, v_f_1707_);
lean_dec(v_inst_1704_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f___redArg(lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_it_1711_, lean_object* v_f_1712_){
_start:
{
lean_object* v_toApplicative_1713_; lean_object* v_toBind_1714_; lean_object* v_toPure_1715_; lean_object* v___f_1716_; lean_object* v___f_1717_; lean_object* v___x_1718_; lean_object* v___f_1719_; lean_object* v___f_1720_; lean_object* v___x_1721_; 
v_toApplicative_1713_ = lean_ctor_get(v_inst_1709_, 0);
lean_inc_ref(v_toApplicative_1713_);
v_toBind_1714_ = lean_ctor_get(v_inst_1709_, 1);
lean_inc_n(v_toBind_1714_, 2);
lean_dec_ref(v_inst_1709_);
v_toPure_1715_ = lean_ctor_get(v_toApplicative_1713_, 1);
lean_inc_n(v_toPure_1715_, 3);
lean_dec_ref(v_toApplicative_1713_);
v___f_1716_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1716_, 0, v_toBind_1714_);
v___f_1717_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1717_, 0, v_toPure_1715_);
v___x_1718_ = lean_box(0);
v___f_1719_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1719_, 0, v___x_1718_);
lean_closure_set(v___f_1719_, 1, v_toPure_1715_);
v___f_1720_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1720_, 0, v_f_1712_);
lean_closure_set(v___f_1720_, 1, v_toPure_1715_);
lean_closure_set(v___f_1720_, 2, v_toBind_1714_);
lean_closure_set(v___f_1720_, 3, v___f_1719_);
lean_closure_set(v___f_1720_, 4, v___f_1717_);
v___x_1721_ = lean_apply_6(v_inst_1710_, v___f_1716_, lean_box(0), lean_box(0), v_it_1711_, v___x_1718_, v___f_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f(lean_object* v_00_u03b1_1722_, lean_object* v_00_u03b2_1723_, lean_object* v_00_u03b3_1724_, lean_object* v_m_1725_, lean_object* v_inst_1726_, lean_object* v_inst_1727_, lean_object* v_inst_1728_, lean_object* v_inst_1729_, lean_object* v_it_1730_, lean_object* v_f_1731_){
_start:
{
lean_object* v_toApplicative_1732_; lean_object* v_toBind_1733_; lean_object* v_toPure_1734_; lean_object* v___f_1735_; lean_object* v___f_1736_; lean_object* v___x_1737_; lean_object* v___f_1738_; lean_object* v___f_1739_; lean_object* v___x_1740_; 
v_toApplicative_1732_ = lean_ctor_get(v_inst_1726_, 0);
lean_inc_ref(v_toApplicative_1732_);
v_toBind_1733_ = lean_ctor_get(v_inst_1726_, 1);
lean_inc_n(v_toBind_1733_, 2);
lean_dec_ref(v_inst_1726_);
v_toPure_1734_ = lean_ctor_get(v_toApplicative_1732_, 1);
lean_inc_n(v_toPure_1734_, 3);
lean_dec_ref(v_toApplicative_1732_);
v___f_1735_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1735_, 0, v_toBind_1733_);
v___f_1736_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1736_, 0, v_toPure_1734_);
v___x_1737_ = lean_box(0);
v___f_1738_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1738_, 0, v___x_1737_);
lean_closure_set(v___f_1738_, 1, v_toPure_1734_);
v___f_1739_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1739_, 0, v_f_1731_);
lean_closure_set(v___f_1739_, 1, v_toPure_1734_);
lean_closure_set(v___f_1739_, 2, v_toBind_1733_);
lean_closure_set(v___f_1739_, 3, v___f_1738_);
lean_closure_set(v___f_1739_, 4, v___f_1736_);
v___x_1740_ = lean_apply_6(v_inst_1728_, v___f_1735_, lean_box(0), lean_box(0), v_it_1730_, v___x_1737_, v___f_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f___boxed(lean_object* v_00_u03b1_1741_, lean_object* v_00_u03b2_1742_, lean_object* v_00_u03b3_1743_, lean_object* v_m_1744_, lean_object* v_inst_1745_, lean_object* v_inst_1746_, lean_object* v_inst_1747_, lean_object* v_inst_1748_, lean_object* v_it_1749_, lean_object* v_f_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Std_IterM_Total_findSome_x3f(v_00_u03b1_1741_, v_00_u03b2_1742_, v_00_u03b3_1743_, v_m_1744_, v_inst_1745_, v_inst_1746_, v_inst_1747_, v_inst_1748_, v_it_1749_, v_f_1750_);
lean_dec(v_inst_1746_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__3(lean_object* v_toPure_1752_, lean_object* v___x_1753_, lean_object* v_x1_1754_, uint8_t v_____do__lift_1755_){
_start:
{
if (v_____do__lift_1755_ == 0)
{
lean_object* v___x_1756_; 
lean_dec(v_x1_1754_);
v___x_1756_ = lean_apply_2(v_toPure_1752_, lean_box(0), v___x_1753_);
return v___x_1756_;
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_dec(v___x_1753_);
v___x_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_x1_1754_);
v___x_1758_ = lean_apply_2(v_toPure_1752_, lean_box(0), v___x_1757_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__3___boxed(lean_object* v_toPure_1759_, lean_object* v___x_1760_, lean_object* v_x1_1761_, lean_object* v_____do__lift_1762_){
_start:
{
uint8_t v_____do__lift_169__boxed_1763_; lean_object* v_res_1764_; 
v_____do__lift_169__boxed_1763_ = lean_unbox(v_____do__lift_1762_);
v_res_1764_ = l_Std_IterM_findM_x3f___redArg___lam__3(v_toPure_1759_, v___x_1760_, v_x1_1761_, v_____do__lift_169__boxed_1763_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__0(lean_object* v_toPure_1765_, lean_object* v___x_1766_, lean_object* v_f_1767_, lean_object* v_toBind_1768_, lean_object* v___f_1769_, lean_object* v___f_1770_, lean_object* v_x1_1771_, lean_object* v_x2_1772_, lean_object* v_x3_1773_){
_start:
{
lean_object* v___f_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
lean_inc(v_x1_1771_);
v___f_1774_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_1774_, 0, v_toPure_1765_);
lean_closure_set(v___f_1774_, 1, v___x_1766_);
lean_closure_set(v___f_1774_, 2, v_x1_1771_);
v___x_1775_ = lean_apply_1(v_f_1767_, v_x1_1771_);
lean_inc_n(v_toBind_1768_, 2);
v___x_1776_ = lean_apply_4(v_toBind_1768_, lean_box(0), lean_box(0), v___x_1775_, v___f_1774_);
v___x_1777_ = lean_apply_4(v_toBind_1768_, lean_box(0), lean_box(0), v___x_1776_, v___f_1769_);
v___x_1778_ = lean_apply_4(v_toBind_1768_, lean_box(0), lean_box(0), v___x_1777_, v___f_1770_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_1779_, lean_object* v___x_1780_, lean_object* v_f_1781_, lean_object* v_toBind_1782_, lean_object* v___f_1783_, lean_object* v___f_1784_, lean_object* v_x1_1785_, lean_object* v_x2_1786_, lean_object* v_x3_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Std_IterM_findM_x3f___redArg___lam__0(v_toPure_1779_, v___x_1780_, v_f_1781_, v_toBind_1782_, v___f_1783_, v___f_1784_, v_x1_1785_, v_x2_1786_, v_x3_1787_);
lean_dec(v_x3_1787_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg(lean_object* v_inst_1789_, lean_object* v_inst_1790_, lean_object* v_it_1791_, lean_object* v_f_1792_){
_start:
{
lean_object* v_toApplicative_1793_; lean_object* v_toBind_1794_; lean_object* v_toPure_1795_; lean_object* v___f_1796_; lean_object* v___f_1797_; lean_object* v___x_1798_; lean_object* v___f_1799_; lean_object* v___f_1800_; lean_object* v___x_1801_; 
v_toApplicative_1793_ = lean_ctor_get(v_inst_1789_, 0);
lean_inc_ref(v_toApplicative_1793_);
v_toBind_1794_ = lean_ctor_get(v_inst_1789_, 1);
lean_inc_n(v_toBind_1794_, 2);
lean_dec_ref(v_inst_1789_);
v_toPure_1795_ = lean_ctor_get(v_toApplicative_1793_, 1);
lean_inc_n(v_toPure_1795_, 3);
lean_dec_ref(v_toApplicative_1793_);
v___f_1796_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1796_, 0, v_toBind_1794_);
v___f_1797_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1797_, 0, v_toPure_1795_);
v___x_1798_ = lean_box(0);
v___f_1799_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1799_, 0, v___x_1798_);
lean_closure_set(v___f_1799_, 1, v_toPure_1795_);
v___f_1800_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1800_, 0, v_toPure_1795_);
lean_closure_set(v___f_1800_, 1, v___x_1798_);
lean_closure_set(v___f_1800_, 2, v_f_1792_);
lean_closure_set(v___f_1800_, 3, v_toBind_1794_);
lean_closure_set(v___f_1800_, 4, v___f_1799_);
lean_closure_set(v___f_1800_, 5, v___f_1797_);
v___x_1801_ = lean_apply_6(v_inst_1790_, v___f_1796_, lean_box(0), lean_box(0), v_it_1791_, v___x_1798_, v___f_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f(lean_object* v_00_u03b1_1802_, lean_object* v_00_u03b2_1803_, lean_object* v_m_1804_, lean_object* v_inst_1805_, lean_object* v_inst_1806_, lean_object* v_inst_1807_, lean_object* v_it_1808_, lean_object* v_f_1809_){
_start:
{
lean_object* v_toApplicative_1810_; lean_object* v_toBind_1811_; lean_object* v_toPure_1812_; lean_object* v___f_1813_; lean_object* v___f_1814_; lean_object* v___x_1815_; lean_object* v___f_1816_; lean_object* v___f_1817_; lean_object* v___x_1818_; 
v_toApplicative_1810_ = lean_ctor_get(v_inst_1805_, 0);
lean_inc_ref(v_toApplicative_1810_);
v_toBind_1811_ = lean_ctor_get(v_inst_1805_, 1);
lean_inc_n(v_toBind_1811_, 2);
lean_dec_ref(v_inst_1805_);
v_toPure_1812_ = lean_ctor_get(v_toApplicative_1810_, 1);
lean_inc_n(v_toPure_1812_, 3);
lean_dec_ref(v_toApplicative_1810_);
v___f_1813_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1813_, 0, v_toBind_1811_);
v___f_1814_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1814_, 0, v_toPure_1812_);
v___x_1815_ = lean_box(0);
v___f_1816_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1816_, 0, v___x_1815_);
lean_closure_set(v___f_1816_, 1, v_toPure_1812_);
v___f_1817_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1817_, 0, v_toPure_1812_);
lean_closure_set(v___f_1817_, 1, v___x_1815_);
lean_closure_set(v___f_1817_, 2, v_f_1809_);
lean_closure_set(v___f_1817_, 3, v_toBind_1811_);
lean_closure_set(v___f_1817_, 4, v___f_1816_);
lean_closure_set(v___f_1817_, 5, v___f_1814_);
v___x_1818_ = lean_apply_6(v_inst_1807_, v___f_1813_, lean_box(0), lean_box(0), v_it_1808_, v___x_1815_, v___f_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___boxed(lean_object* v_00_u03b1_1819_, lean_object* v_00_u03b2_1820_, lean_object* v_m_1821_, lean_object* v_inst_1822_, lean_object* v_inst_1823_, lean_object* v_inst_1824_, lean_object* v_it_1825_, lean_object* v_f_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Std_IterM_findM_x3f(v_00_u03b1_1819_, v_00_u03b2_1820_, v_m_1821_, v_inst_1822_, v_inst_1823_, v_inst_1824_, v_it_1825_, v_f_1826_);
lean_dec(v_inst_1823_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f___redArg(lean_object* v_inst_1828_, lean_object* v_inst_1829_, lean_object* v_it_1830_, lean_object* v_f_1831_){
_start:
{
lean_object* v_toApplicative_1832_; lean_object* v_toBind_1833_; lean_object* v_toPure_1834_; lean_object* v___f_1835_; lean_object* v___f_1836_; lean_object* v___x_1837_; lean_object* v___f_1838_; lean_object* v___f_1839_; lean_object* v___x_1840_; 
v_toApplicative_1832_ = lean_ctor_get(v_inst_1828_, 0);
lean_inc_ref(v_toApplicative_1832_);
v_toBind_1833_ = lean_ctor_get(v_inst_1828_, 1);
lean_inc_n(v_toBind_1833_, 2);
lean_dec_ref(v_inst_1828_);
v_toPure_1834_ = lean_ctor_get(v_toApplicative_1832_, 1);
lean_inc_n(v_toPure_1834_, 3);
lean_dec_ref(v_toApplicative_1832_);
v___f_1835_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1835_, 0, v_toBind_1833_);
v___f_1836_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1836_, 0, v_toPure_1834_);
v___x_1837_ = lean_box(0);
v___f_1838_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1838_, 0, v___x_1837_);
lean_closure_set(v___f_1838_, 1, v_toPure_1834_);
v___f_1839_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1839_, 0, v_toPure_1834_);
lean_closure_set(v___f_1839_, 1, v___x_1837_);
lean_closure_set(v___f_1839_, 2, v_f_1831_);
lean_closure_set(v___f_1839_, 3, v_toBind_1833_);
lean_closure_set(v___f_1839_, 4, v___f_1838_);
lean_closure_set(v___f_1839_, 5, v___f_1836_);
v___x_1840_ = lean_apply_6(v_inst_1829_, v___f_1835_, lean_box(0), lean_box(0), v_it_1830_, v___x_1837_, v___f_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f(lean_object* v_00_u03b1_1841_, lean_object* v_00_u03b2_1842_, lean_object* v_m_1843_, lean_object* v_inst_1844_, lean_object* v_inst_1845_, lean_object* v_inst_1846_, lean_object* v_it_1847_, lean_object* v_f_1848_){
_start:
{
lean_object* v_toApplicative_1849_; lean_object* v_toBind_1850_; lean_object* v_toPure_1851_; lean_object* v___f_1852_; lean_object* v___f_1853_; lean_object* v___x_1854_; lean_object* v___f_1855_; lean_object* v___f_1856_; lean_object* v___x_1857_; 
v_toApplicative_1849_ = lean_ctor_get(v_inst_1844_, 0);
lean_inc_ref(v_toApplicative_1849_);
v_toBind_1850_ = lean_ctor_get(v_inst_1844_, 1);
lean_inc_n(v_toBind_1850_, 2);
lean_dec_ref(v_inst_1844_);
v_toPure_1851_ = lean_ctor_get(v_toApplicative_1849_, 1);
lean_inc_n(v_toPure_1851_, 3);
lean_dec_ref(v_toApplicative_1849_);
v___f_1852_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1852_, 0, v_toBind_1850_);
v___f_1853_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1853_, 0, v_toPure_1851_);
v___x_1854_ = lean_box(0);
v___f_1855_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1855_, 0, v___x_1854_);
lean_closure_set(v___f_1855_, 1, v_toPure_1851_);
v___f_1856_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1856_, 0, v_toPure_1851_);
lean_closure_set(v___f_1856_, 1, v___x_1854_);
lean_closure_set(v___f_1856_, 2, v_f_1848_);
lean_closure_set(v___f_1856_, 3, v_toBind_1850_);
lean_closure_set(v___f_1856_, 4, v___f_1855_);
lean_closure_set(v___f_1856_, 5, v___f_1853_);
v___x_1857_ = lean_apply_6(v_inst_1846_, v___f_1852_, lean_box(0), lean_box(0), v_it_1847_, v___x_1854_, v___f_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f___boxed(lean_object* v_00_u03b1_1858_, lean_object* v_00_u03b2_1859_, lean_object* v_m_1860_, lean_object* v_inst_1861_, lean_object* v_inst_1862_, lean_object* v_inst_1863_, lean_object* v_it_1864_, lean_object* v_f_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Std_IterM_Partial_findM_x3f(v_00_u03b1_1858_, v_00_u03b2_1859_, v_m_1860_, v_inst_1861_, v_inst_1862_, v_inst_1863_, v_it_1864_, v_f_1865_);
lean_dec(v_inst_1862_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f___redArg(lean_object* v_inst_1867_, lean_object* v_inst_1868_, lean_object* v_it_1869_, lean_object* v_f_1870_){
_start:
{
lean_object* v_toApplicative_1871_; lean_object* v_toBind_1872_; lean_object* v_toPure_1873_; lean_object* v___f_1874_; lean_object* v___f_1875_; lean_object* v___x_1876_; lean_object* v___f_1877_; lean_object* v___f_1878_; lean_object* v___x_1879_; 
v_toApplicative_1871_ = lean_ctor_get(v_inst_1867_, 0);
lean_inc_ref(v_toApplicative_1871_);
v_toBind_1872_ = lean_ctor_get(v_inst_1867_, 1);
lean_inc_n(v_toBind_1872_, 2);
lean_dec_ref(v_inst_1867_);
v_toPure_1873_ = lean_ctor_get(v_toApplicative_1871_, 1);
lean_inc_n(v_toPure_1873_, 3);
lean_dec_ref(v_toApplicative_1871_);
v___f_1874_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1874_, 0, v_toBind_1872_);
v___f_1875_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1875_, 0, v_toPure_1873_);
v___x_1876_ = lean_box(0);
v___f_1877_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1877_, 0, v___x_1876_);
lean_closure_set(v___f_1877_, 1, v_toPure_1873_);
v___f_1878_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1878_, 0, v_toPure_1873_);
lean_closure_set(v___f_1878_, 1, v___x_1876_);
lean_closure_set(v___f_1878_, 2, v_f_1870_);
lean_closure_set(v___f_1878_, 3, v_toBind_1872_);
lean_closure_set(v___f_1878_, 4, v___f_1877_);
lean_closure_set(v___f_1878_, 5, v___f_1875_);
v___x_1879_ = lean_apply_6(v_inst_1868_, v___f_1874_, lean_box(0), lean_box(0), v_it_1869_, v___x_1876_, v___f_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f(lean_object* v_00_u03b1_1880_, lean_object* v_00_u03b2_1881_, lean_object* v_m_1882_, lean_object* v_inst_1883_, lean_object* v_inst_1884_, lean_object* v_inst_1885_, lean_object* v_inst_1886_, lean_object* v_it_1887_, lean_object* v_f_1888_){
_start:
{
lean_object* v_toApplicative_1889_; lean_object* v_toBind_1890_; lean_object* v_toPure_1891_; lean_object* v___f_1892_; lean_object* v___f_1893_; lean_object* v___x_1894_; lean_object* v___f_1895_; lean_object* v___f_1896_; lean_object* v___x_1897_; 
v_toApplicative_1889_ = lean_ctor_get(v_inst_1883_, 0);
lean_inc_ref(v_toApplicative_1889_);
v_toBind_1890_ = lean_ctor_get(v_inst_1883_, 1);
lean_inc_n(v_toBind_1890_, 2);
lean_dec_ref(v_inst_1883_);
v_toPure_1891_ = lean_ctor_get(v_toApplicative_1889_, 1);
lean_inc_n(v_toPure_1891_, 3);
lean_dec_ref(v_toApplicative_1889_);
v___f_1892_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1892_, 0, v_toBind_1890_);
v___f_1893_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1893_, 0, v_toPure_1891_);
v___x_1894_ = lean_box(0);
v___f_1895_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1895_, 0, v___x_1894_);
lean_closure_set(v___f_1895_, 1, v_toPure_1891_);
v___f_1896_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1896_, 0, v_toPure_1891_);
lean_closure_set(v___f_1896_, 1, v___x_1894_);
lean_closure_set(v___f_1896_, 2, v_f_1888_);
lean_closure_set(v___f_1896_, 3, v_toBind_1890_);
lean_closure_set(v___f_1896_, 4, v___f_1895_);
lean_closure_set(v___f_1896_, 5, v___f_1893_);
v___x_1897_ = lean_apply_6(v_inst_1885_, v___f_1892_, lean_box(0), lean_box(0), v_it_1887_, v___x_1894_, v___f_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f___boxed(lean_object* v_00_u03b1_1898_, lean_object* v_00_u03b2_1899_, lean_object* v_m_1900_, lean_object* v_inst_1901_, lean_object* v_inst_1902_, lean_object* v_inst_1903_, lean_object* v_inst_1904_, lean_object* v_it_1905_, lean_object* v_f_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Std_IterM_Total_findM_x3f(v_00_u03b1_1898_, v_00_u03b2_1899_, v_m_1900_, v_inst_1901_, v_inst_1902_, v_inst_1903_, v_inst_1904_, v_it_1905_, v_f_1906_);
lean_dec(v_inst_1902_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg___lam__4(lean_object* v_toPure_1908_, lean_object* v___x_1909_, lean_object* v_f_1910_, lean_object* v_toBind_1911_, lean_object* v___f_1912_, lean_object* v___f_1913_, lean_object* v_x1_1914_, lean_object* v_x2_1915_, lean_object* v_x3_1916_){
_start:
{
lean_object* v___f_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
lean_inc(v_x1_1914_);
lean_inc(v_toPure_1908_);
v___f_1917_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_1917_, 0, v_toPure_1908_);
lean_closure_set(v___f_1917_, 1, v___x_1909_);
lean_closure_set(v___f_1917_, 2, v_x1_1914_);
v___x_1918_ = lean_apply_1(v_f_1910_, v_x1_1914_);
v___x_1919_ = lean_apply_2(v_toPure_1908_, lean_box(0), v___x_1918_);
lean_inc_n(v_toBind_1911_, 2);
v___x_1920_ = lean_apply_4(v_toBind_1911_, lean_box(0), lean_box(0), v___x_1919_, v___f_1917_);
v___x_1921_ = lean_apply_4(v_toBind_1911_, lean_box(0), lean_box(0), v___x_1920_, v___f_1912_);
v___x_1922_ = lean_apply_4(v_toBind_1911_, lean_box(0), lean_box(0), v___x_1921_, v___f_1913_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg___lam__4___boxed(lean_object* v_toPure_1923_, lean_object* v___x_1924_, lean_object* v_f_1925_, lean_object* v_toBind_1926_, lean_object* v___f_1927_, lean_object* v___f_1928_, lean_object* v_x1_1929_, lean_object* v_x2_1930_, lean_object* v_x3_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Std_IterM_find_x3f___redArg___lam__4(v_toPure_1923_, v___x_1924_, v_f_1925_, v_toBind_1926_, v___f_1927_, v___f_1928_, v_x1_1929_, v_x2_1930_, v_x3_1931_);
lean_dec(v_x3_1931_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg(lean_object* v_inst_1933_, lean_object* v_inst_1934_, lean_object* v_it_1935_, lean_object* v_f_1936_){
_start:
{
lean_object* v_toApplicative_1937_; lean_object* v_toBind_1938_; lean_object* v_toPure_1939_; lean_object* v___f_1940_; lean_object* v___f_1941_; lean_object* v___x_1942_; lean_object* v___f_1943_; lean_object* v___f_1944_; lean_object* v___x_1945_; 
v_toApplicative_1937_ = lean_ctor_get(v_inst_1933_, 0);
lean_inc_ref(v_toApplicative_1937_);
v_toBind_1938_ = lean_ctor_get(v_inst_1933_, 1);
lean_inc_n(v_toBind_1938_, 2);
lean_dec_ref(v_inst_1933_);
v_toPure_1939_ = lean_ctor_get(v_toApplicative_1937_, 1);
lean_inc_n(v_toPure_1939_, 3);
lean_dec_ref(v_toApplicative_1937_);
v___f_1940_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1940_, 0, v_toBind_1938_);
v___f_1941_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1941_, 0, v_toPure_1939_);
v___x_1942_ = lean_box(0);
v___f_1943_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1943_, 0, v___x_1942_);
lean_closure_set(v___f_1943_, 1, v_toPure_1939_);
v___f_1944_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_1944_, 0, v_toPure_1939_);
lean_closure_set(v___f_1944_, 1, v___x_1942_);
lean_closure_set(v___f_1944_, 2, v_f_1936_);
lean_closure_set(v___f_1944_, 3, v_toBind_1938_);
lean_closure_set(v___f_1944_, 4, v___f_1943_);
lean_closure_set(v___f_1944_, 5, v___f_1941_);
v___x_1945_ = lean_apply_6(v_inst_1934_, v___f_1940_, lean_box(0), lean_box(0), v_it_1935_, v___x_1942_, v___f_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f(lean_object* v_00_u03b1_1946_, lean_object* v_00_u03b2_1947_, lean_object* v_m_1948_, lean_object* v_inst_1949_, lean_object* v_inst_1950_, lean_object* v_inst_1951_, lean_object* v_it_1952_, lean_object* v_f_1953_){
_start:
{
lean_object* v_toApplicative_1954_; lean_object* v_toBind_1955_; lean_object* v_toPure_1956_; lean_object* v___f_1957_; lean_object* v___f_1958_; lean_object* v___x_1959_; lean_object* v___f_1960_; lean_object* v___f_1961_; lean_object* v___x_1962_; 
v_toApplicative_1954_ = lean_ctor_get(v_inst_1949_, 0);
lean_inc_ref(v_toApplicative_1954_);
v_toBind_1955_ = lean_ctor_get(v_inst_1949_, 1);
lean_inc_n(v_toBind_1955_, 2);
lean_dec_ref(v_inst_1949_);
v_toPure_1956_ = lean_ctor_get(v_toApplicative_1954_, 1);
lean_inc_n(v_toPure_1956_, 3);
lean_dec_ref(v_toApplicative_1954_);
v___f_1957_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1957_, 0, v_toBind_1955_);
v___f_1958_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1958_, 0, v_toPure_1956_);
v___x_1959_ = lean_box(0);
v___f_1960_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1960_, 0, v___x_1959_);
lean_closure_set(v___f_1960_, 1, v_toPure_1956_);
v___f_1961_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_1961_, 0, v_toPure_1956_);
lean_closure_set(v___f_1961_, 1, v___x_1959_);
lean_closure_set(v___f_1961_, 2, v_f_1953_);
lean_closure_set(v___f_1961_, 3, v_toBind_1955_);
lean_closure_set(v___f_1961_, 4, v___f_1960_);
lean_closure_set(v___f_1961_, 5, v___f_1958_);
v___x_1962_ = lean_apply_6(v_inst_1951_, v___f_1957_, lean_box(0), lean_box(0), v_it_1952_, v___x_1959_, v___f_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___boxed(lean_object* v_00_u03b1_1963_, lean_object* v_00_u03b2_1964_, lean_object* v_m_1965_, lean_object* v_inst_1966_, lean_object* v_inst_1967_, lean_object* v_inst_1968_, lean_object* v_it_1969_, lean_object* v_f_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Std_IterM_find_x3f(v_00_u03b1_1963_, v_00_u03b2_1964_, v_m_1965_, v_inst_1966_, v_inst_1967_, v_inst_1968_, v_it_1969_, v_f_1970_);
lean_dec(v_inst_1967_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f___redArg(lean_object* v_inst_1972_, lean_object* v_inst_1973_, lean_object* v_it_1974_, lean_object* v_f_1975_){
_start:
{
lean_object* v_toApplicative_1976_; lean_object* v_toBind_1977_; lean_object* v_toPure_1978_; lean_object* v___f_1979_; lean_object* v___f_1980_; lean_object* v___x_1981_; lean_object* v___f_1982_; lean_object* v___f_1983_; lean_object* v___x_1984_; 
v_toApplicative_1976_ = lean_ctor_get(v_inst_1972_, 0);
lean_inc_ref(v_toApplicative_1976_);
v_toBind_1977_ = lean_ctor_get(v_inst_1972_, 1);
lean_inc_n(v_toBind_1977_, 2);
lean_dec_ref(v_inst_1972_);
v_toPure_1978_ = lean_ctor_get(v_toApplicative_1976_, 1);
lean_inc_n(v_toPure_1978_, 3);
lean_dec_ref(v_toApplicative_1976_);
v___f_1979_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1979_, 0, v_toBind_1977_);
v___f_1980_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1980_, 0, v_toPure_1978_);
v___x_1981_ = lean_box(0);
v___f_1982_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1982_, 0, v___x_1981_);
lean_closure_set(v___f_1982_, 1, v_toPure_1978_);
v___f_1983_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_1983_, 0, v_toPure_1978_);
lean_closure_set(v___f_1983_, 1, v___x_1981_);
lean_closure_set(v___f_1983_, 2, v_f_1975_);
lean_closure_set(v___f_1983_, 3, v_toBind_1977_);
lean_closure_set(v___f_1983_, 4, v___f_1982_);
lean_closure_set(v___f_1983_, 5, v___f_1980_);
v___x_1984_ = lean_apply_6(v_inst_1973_, v___f_1979_, lean_box(0), lean_box(0), v_it_1974_, v___x_1981_, v___f_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f(lean_object* v_00_u03b1_1985_, lean_object* v_00_u03b2_1986_, lean_object* v_m_1987_, lean_object* v_inst_1988_, lean_object* v_inst_1989_, lean_object* v_inst_1990_, lean_object* v_it_1991_, lean_object* v_f_1992_){
_start:
{
lean_object* v_toApplicative_1993_; lean_object* v_toBind_1994_; lean_object* v_toPure_1995_; lean_object* v___f_1996_; lean_object* v___f_1997_; lean_object* v___x_1998_; lean_object* v___f_1999_; lean_object* v___f_2000_; lean_object* v___x_2001_; 
v_toApplicative_1993_ = lean_ctor_get(v_inst_1988_, 0);
lean_inc_ref(v_toApplicative_1993_);
v_toBind_1994_ = lean_ctor_get(v_inst_1988_, 1);
lean_inc_n(v_toBind_1994_, 2);
lean_dec_ref(v_inst_1988_);
v_toPure_1995_ = lean_ctor_get(v_toApplicative_1993_, 1);
lean_inc_n(v_toPure_1995_, 3);
lean_dec_ref(v_toApplicative_1993_);
v___f_1996_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1996_, 0, v_toBind_1994_);
v___f_1997_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1997_, 0, v_toPure_1995_);
v___x_1998_ = lean_box(0);
v___f_1999_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1999_, 0, v___x_1998_);
lean_closure_set(v___f_1999_, 1, v_toPure_1995_);
v___f_2000_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_2000_, 0, v_toPure_1995_);
lean_closure_set(v___f_2000_, 1, v___x_1998_);
lean_closure_set(v___f_2000_, 2, v_f_1992_);
lean_closure_set(v___f_2000_, 3, v_toBind_1994_);
lean_closure_set(v___f_2000_, 4, v___f_1999_);
lean_closure_set(v___f_2000_, 5, v___f_1997_);
v___x_2001_ = lean_apply_6(v_inst_1990_, v___f_1996_, lean_box(0), lean_box(0), v_it_1991_, v___x_1998_, v___f_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f___boxed(lean_object* v_00_u03b1_2002_, lean_object* v_00_u03b2_2003_, lean_object* v_m_2004_, lean_object* v_inst_2005_, lean_object* v_inst_2006_, lean_object* v_inst_2007_, lean_object* v_it_2008_, lean_object* v_f_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Std_IterM_Partial_find_x3f(v_00_u03b1_2002_, v_00_u03b2_2003_, v_m_2004_, v_inst_2005_, v_inst_2006_, v_inst_2007_, v_it_2008_, v_f_2009_);
lean_dec(v_inst_2006_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f___redArg(lean_object* v_inst_2011_, lean_object* v_inst_2012_, lean_object* v_it_2013_, lean_object* v_f_2014_){
_start:
{
lean_object* v_toApplicative_2015_; lean_object* v_toBind_2016_; lean_object* v_toPure_2017_; lean_object* v___f_2018_; lean_object* v___f_2019_; lean_object* v___x_2020_; lean_object* v___f_2021_; lean_object* v___f_2022_; lean_object* v___x_2023_; 
v_toApplicative_2015_ = lean_ctor_get(v_inst_2011_, 0);
lean_inc_ref(v_toApplicative_2015_);
v_toBind_2016_ = lean_ctor_get(v_inst_2011_, 1);
lean_inc_n(v_toBind_2016_, 2);
lean_dec_ref(v_inst_2011_);
v_toPure_2017_ = lean_ctor_get(v_toApplicative_2015_, 1);
lean_inc_n(v_toPure_2017_, 3);
lean_dec_ref(v_toApplicative_2015_);
v___f_2018_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2018_, 0, v_toBind_2016_);
v___f_2019_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2019_, 0, v_toPure_2017_);
v___x_2020_ = lean_box(0);
v___f_2021_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2021_, 0, v___x_2020_);
lean_closure_set(v___f_2021_, 1, v_toPure_2017_);
v___f_2022_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_2022_, 0, v_toPure_2017_);
lean_closure_set(v___f_2022_, 1, v___x_2020_);
lean_closure_set(v___f_2022_, 2, v_f_2014_);
lean_closure_set(v___f_2022_, 3, v_toBind_2016_);
lean_closure_set(v___f_2022_, 4, v___f_2021_);
lean_closure_set(v___f_2022_, 5, v___f_2019_);
v___x_2023_ = lean_apply_6(v_inst_2012_, v___f_2018_, lean_box(0), lean_box(0), v_it_2013_, v___x_2020_, v___f_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f(lean_object* v_00_u03b1_2024_, lean_object* v_00_u03b2_2025_, lean_object* v_m_2026_, lean_object* v_inst_2027_, lean_object* v_inst_2028_, lean_object* v_inst_2029_, lean_object* v_inst_2030_, lean_object* v_it_2031_, lean_object* v_f_2032_){
_start:
{
lean_object* v_toApplicative_2033_; lean_object* v_toBind_2034_; lean_object* v_toPure_2035_; lean_object* v___f_2036_; lean_object* v___f_2037_; lean_object* v___x_2038_; lean_object* v___f_2039_; lean_object* v___f_2040_; lean_object* v___x_2041_; 
v_toApplicative_2033_ = lean_ctor_get(v_inst_2027_, 0);
lean_inc_ref(v_toApplicative_2033_);
v_toBind_2034_ = lean_ctor_get(v_inst_2027_, 1);
lean_inc_n(v_toBind_2034_, 2);
lean_dec_ref(v_inst_2027_);
v_toPure_2035_ = lean_ctor_get(v_toApplicative_2033_, 1);
lean_inc_n(v_toPure_2035_, 3);
lean_dec_ref(v_toApplicative_2033_);
v___f_2036_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2036_, 0, v_toBind_2034_);
v___f_2037_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2037_, 0, v_toPure_2035_);
v___x_2038_ = lean_box(0);
v___f_2039_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2039_, 0, v___x_2038_);
lean_closure_set(v___f_2039_, 1, v_toPure_2035_);
v___f_2040_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_2040_, 0, v_toPure_2035_);
lean_closure_set(v___f_2040_, 1, v___x_2038_);
lean_closure_set(v___f_2040_, 2, v_f_2032_);
lean_closure_set(v___f_2040_, 3, v_toBind_2034_);
lean_closure_set(v___f_2040_, 4, v___f_2039_);
lean_closure_set(v___f_2040_, 5, v___f_2037_);
v___x_2041_ = lean_apply_6(v_inst_2029_, v___f_2036_, lean_box(0), lean_box(0), v_it_2031_, v___x_2038_, v___f_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f___boxed(lean_object* v_00_u03b1_2042_, lean_object* v_00_u03b2_2043_, lean_object* v_m_2044_, lean_object* v_inst_2045_, lean_object* v_inst_2046_, lean_object* v_inst_2047_, lean_object* v_inst_2048_, lean_object* v_it_2049_, lean_object* v_f_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Std_IterM_Total_find_x3f(v_00_u03b1_2042_, v_00_u03b2_2043_, v_m_2044_, v_inst_2045_, v_inst_2046_, v_inst_2047_, v_inst_2048_, v_it_2049_, v_f_2050_);
lean_dec(v_inst_2046_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg___lam__0(lean_object* v_toBind_2052_, lean_object* v_x_2053_, lean_object* v_x_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_apply_4(v_toBind_2052_, lean_box(0), lean_box(0), v___y_2056_, v___y_2055_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg___lam__1(lean_object* v_toPure_2058_, lean_object* v_b_2059_, lean_object* v_x_2060_, lean_object* v_x_2061_){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2062_, 0, v_b_2059_);
v___x_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
v___x_2064_ = lean_apply_2(v_toPure_2058_, lean_box(0), v___x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg___lam__1___boxed(lean_object* v_toPure_2065_, lean_object* v_b_2066_, lean_object* v_x_2067_, lean_object* v_x_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Std_IterM_first_x3f___redArg___lam__1(v_toPure_2065_, v_b_2066_, v_x_2067_, v_x_2068_);
lean_dec(v_x_2068_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg(lean_object* v_inst_2070_, lean_object* v_inst_2071_, lean_object* v_it_2072_){
_start:
{
lean_object* v_toApplicative_2073_; lean_object* v_toBind_2074_; lean_object* v_toPure_2075_; lean_object* v___f_2076_; lean_object* v___f_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v_toApplicative_2073_ = lean_ctor_get(v_inst_2070_, 0);
lean_inc_ref(v_toApplicative_2073_);
v_toBind_2074_ = lean_ctor_get(v_inst_2070_, 1);
lean_inc(v_toBind_2074_);
lean_dec_ref(v_inst_2070_);
v_toPure_2075_ = lean_ctor_get(v_toApplicative_2073_, 1);
lean_inc(v_toPure_2075_);
lean_dec_ref(v_toApplicative_2073_);
v___f_2076_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2076_, 0, v_toBind_2074_);
v___f_2077_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2077_, 0, v_toPure_2075_);
v___x_2078_ = lean_box(0);
v___x_2079_ = lean_apply_6(v_inst_2071_, v___f_2076_, lean_box(0), lean_box(0), v_it_2072_, v___x_2078_, v___f_2077_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f(lean_object* v_00_u03b1_2080_, lean_object* v_00_u03b2_2081_, lean_object* v_m_2082_, lean_object* v_inst_2083_, lean_object* v_inst_2084_, lean_object* v_inst_2085_, lean_object* v_it_2086_){
_start:
{
lean_object* v_toApplicative_2087_; lean_object* v_toBind_2088_; lean_object* v_toPure_2089_; lean_object* v___f_2090_; lean_object* v___f_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v_toApplicative_2087_ = lean_ctor_get(v_inst_2083_, 0);
lean_inc_ref(v_toApplicative_2087_);
v_toBind_2088_ = lean_ctor_get(v_inst_2083_, 1);
lean_inc(v_toBind_2088_);
lean_dec_ref(v_inst_2083_);
v_toPure_2089_ = lean_ctor_get(v_toApplicative_2087_, 1);
lean_inc(v_toPure_2089_);
lean_dec_ref(v_toApplicative_2087_);
v___f_2090_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2090_, 0, v_toBind_2088_);
v___f_2091_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2091_, 0, v_toPure_2089_);
v___x_2092_ = lean_box(0);
v___x_2093_ = lean_apply_6(v_inst_2085_, v___f_2090_, lean_box(0), lean_box(0), v_it_2086_, v___x_2092_, v___f_2091_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___boxed(lean_object* v_00_u03b1_2094_, lean_object* v_00_u03b2_2095_, lean_object* v_m_2096_, lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_it_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Std_IterM_first_x3f(v_00_u03b1_2094_, v_00_u03b2_2095_, v_m_2096_, v_inst_2097_, v_inst_2098_, v_inst_2099_, v_it_2100_);
lean_dec(v_inst_2098_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_first_x3f___redArg(lean_object* v_inst_2102_, lean_object* v_inst_2103_, lean_object* v_it_2104_){
_start:
{
lean_object* v_toApplicative_2105_; lean_object* v_toBind_2106_; lean_object* v_toPure_2107_; lean_object* v___f_2108_; lean_object* v___f_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v_toApplicative_2105_ = lean_ctor_get(v_inst_2102_, 0);
lean_inc_ref(v_toApplicative_2105_);
v_toBind_2106_ = lean_ctor_get(v_inst_2102_, 1);
lean_inc(v_toBind_2106_);
lean_dec_ref(v_inst_2102_);
v_toPure_2107_ = lean_ctor_get(v_toApplicative_2105_, 1);
lean_inc(v_toPure_2107_);
lean_dec_ref(v_toApplicative_2105_);
v___f_2108_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2108_, 0, v_toBind_2106_);
v___f_2109_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2109_, 0, v_toPure_2107_);
v___x_2110_ = lean_box(0);
v___x_2111_ = lean_apply_6(v_inst_2103_, v___f_2108_, lean_box(0), lean_box(0), v_it_2104_, v___x_2110_, v___f_2109_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_first_x3f(lean_object* v_00_u03b1_2112_, lean_object* v_00_u03b2_2113_, lean_object* v_m_2114_, lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_inst_2117_, lean_object* v_inst_2118_, lean_object* v_it_2119_){
_start:
{
lean_object* v_toApplicative_2120_; lean_object* v_toBind_2121_; lean_object* v_toPure_2122_; lean_object* v___f_2123_; lean_object* v___f_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_toApplicative_2120_ = lean_ctor_get(v_inst_2115_, 0);
lean_inc_ref(v_toApplicative_2120_);
v_toBind_2121_ = lean_ctor_get(v_inst_2115_, 1);
lean_inc(v_toBind_2121_);
lean_dec_ref(v_inst_2115_);
v_toPure_2122_ = lean_ctor_get(v_toApplicative_2120_, 1);
lean_inc(v_toPure_2122_);
lean_dec_ref(v_toApplicative_2120_);
v___f_2123_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2123_, 0, v_toBind_2121_);
v___f_2124_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2124_, 0, v_toPure_2122_);
v___x_2125_ = lean_box(0);
v___x_2126_ = lean_apply_6(v_inst_2117_, v___f_2123_, lean_box(0), lean_box(0), v_it_2119_, v___x_2125_, v___f_2124_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_first_x3f___boxed(lean_object* v_00_u03b1_2127_, lean_object* v_00_u03b2_2128_, lean_object* v_m_2129_, lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v_inst_2132_, lean_object* v_inst_2133_, lean_object* v_it_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Std_IterM_Total_first_x3f(v_00_u03b1_2127_, v_00_u03b2_2128_, v_m_2129_, v_inst_2130_, v_inst_2131_, v_inst_2132_, v_inst_2133_, v_it_2134_);
lean_dec(v_inst_2131_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___redArg___lam__1(lean_object* v_toPure_2139_, lean_object* v_x_2140_, lean_object* v_x_2141_, uint8_t v_x_2142_){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = ((lean_object*)(l_Std_IterM_isEmpty___redArg___lam__1___closed__0));
v___x_2144_ = lean_apply_2(v_toPure_2139_, lean_box(0), v___x_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___redArg___lam__1___boxed(lean_object* v_toPure_2145_, lean_object* v_x_2146_, lean_object* v_x_2147_, lean_object* v_x_2148_){
_start:
{
uint8_t v_x_79__boxed_2149_; lean_object* v_res_2150_; 
v_x_79__boxed_2149_ = lean_unbox(v_x_2148_);
v_res_2150_ = l_Std_IterM_isEmpty___redArg___lam__1(v_toPure_2145_, v_x_2146_, v_x_2147_, v_x_79__boxed_2149_);
lean_dec(v_x_2146_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___redArg(lean_object* v_inst_2151_, lean_object* v_inst_2152_, lean_object* v_it_2153_){
_start:
{
lean_object* v_toApplicative_2154_; lean_object* v_toBind_2155_; lean_object* v_toPure_2156_; lean_object* v___f_2157_; lean_object* v___f_2158_; uint8_t v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v_toApplicative_2154_ = lean_ctor_get(v_inst_2151_, 0);
lean_inc_ref(v_toApplicative_2154_);
v_toBind_2155_ = lean_ctor_get(v_inst_2151_, 1);
lean_inc(v_toBind_2155_);
lean_dec_ref(v_inst_2151_);
v_toPure_2156_ = lean_ctor_get(v_toApplicative_2154_, 1);
lean_inc(v_toPure_2156_);
lean_dec_ref(v_toApplicative_2154_);
v___f_2157_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2157_, 0, v_toBind_2155_);
v___f_2158_ = lean_alloc_closure((void*)(l_Std_IterM_isEmpty___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2158_, 0, v_toPure_2156_);
v___x_2159_ = 1;
v___x_2160_ = lean_box(v___x_2159_);
v___x_2161_ = lean_apply_6(v_inst_2152_, v___f_2157_, lean_box(0), lean_box(0), v_it_2153_, v___x_2160_, v___f_2158_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty(lean_object* v_00_u03b1_2162_, lean_object* v_00_u03b2_2163_, lean_object* v_m_2164_, lean_object* v_inst_2165_, lean_object* v_inst_2166_, lean_object* v_inst_2167_, lean_object* v_it_2168_){
_start:
{
lean_object* v_toApplicative_2169_; lean_object* v_toBind_2170_; lean_object* v_toPure_2171_; lean_object* v___f_2172_; lean_object* v___f_2173_; uint8_t v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v_toApplicative_2169_ = lean_ctor_get(v_inst_2165_, 0);
lean_inc_ref(v_toApplicative_2169_);
v_toBind_2170_ = lean_ctor_get(v_inst_2165_, 1);
lean_inc(v_toBind_2170_);
lean_dec_ref(v_inst_2165_);
v_toPure_2171_ = lean_ctor_get(v_toApplicative_2169_, 1);
lean_inc(v_toPure_2171_);
lean_dec_ref(v_toApplicative_2169_);
v___f_2172_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2172_, 0, v_toBind_2170_);
v___f_2173_ = lean_alloc_closure((void*)(l_Std_IterM_isEmpty___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2173_, 0, v_toPure_2171_);
v___x_2174_ = 1;
v___x_2175_ = lean_box(v___x_2174_);
v___x_2176_ = lean_apply_6(v_inst_2167_, v___f_2172_, lean_box(0), lean_box(0), v_it_2168_, v___x_2175_, v___f_2173_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___boxed(lean_object* v_00_u03b1_2177_, lean_object* v_00_u03b2_2178_, lean_object* v_m_2179_, lean_object* v_inst_2180_, lean_object* v_inst_2181_, lean_object* v_inst_2182_, lean_object* v_it_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Std_IterM_isEmpty(v_00_u03b1_2177_, v_00_u03b2_2178_, v_m_2179_, v_inst_2180_, v_inst_2181_, v_inst_2182_, v_it_2183_);
lean_dec(v_inst_2181_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_isEmpty___redArg(lean_object* v_inst_2185_, lean_object* v_inst_2186_, lean_object* v_it_2187_){
_start:
{
lean_object* v_toApplicative_2188_; lean_object* v_toBind_2189_; lean_object* v_toPure_2190_; lean_object* v___f_2191_; lean_object* v___f_2192_; uint8_t v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v_toApplicative_2188_ = lean_ctor_get(v_inst_2185_, 0);
lean_inc_ref(v_toApplicative_2188_);
v_toBind_2189_ = lean_ctor_get(v_inst_2185_, 1);
lean_inc(v_toBind_2189_);
lean_dec_ref(v_inst_2185_);
v_toPure_2190_ = lean_ctor_get(v_toApplicative_2188_, 1);
lean_inc(v_toPure_2190_);
lean_dec_ref(v_toApplicative_2188_);
v___f_2191_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2191_, 0, v_toBind_2189_);
v___f_2192_ = lean_alloc_closure((void*)(l_Std_IterM_isEmpty___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2192_, 0, v_toPure_2190_);
v___x_2193_ = 1;
v___x_2194_ = lean_box(v___x_2193_);
v___x_2195_ = lean_apply_6(v_inst_2186_, v___f_2191_, lean_box(0), lean_box(0), v_it_2187_, v___x_2194_, v___f_2192_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_isEmpty(lean_object* v_00_u03b1_2196_, lean_object* v_00_u03b2_2197_, lean_object* v_m_2198_, lean_object* v_inst_2199_, lean_object* v_inst_2200_, lean_object* v_inst_2201_, lean_object* v_inst_2202_, lean_object* v_it_2203_){
_start:
{
lean_object* v_toApplicative_2204_; lean_object* v_toBind_2205_; lean_object* v_toPure_2206_; lean_object* v___f_2207_; lean_object* v___f_2208_; uint8_t v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v_toApplicative_2204_ = lean_ctor_get(v_inst_2199_, 0);
lean_inc_ref(v_toApplicative_2204_);
v_toBind_2205_ = lean_ctor_get(v_inst_2199_, 1);
lean_inc(v_toBind_2205_);
lean_dec_ref(v_inst_2199_);
v_toPure_2206_ = lean_ctor_get(v_toApplicative_2204_, 1);
lean_inc(v_toPure_2206_);
lean_dec_ref(v_toApplicative_2204_);
v___f_2207_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2207_, 0, v_toBind_2205_);
v___f_2208_ = lean_alloc_closure((void*)(l_Std_IterM_isEmpty___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2208_, 0, v_toPure_2206_);
v___x_2209_ = 1;
v___x_2210_ = lean_box(v___x_2209_);
v___x_2211_ = lean_apply_6(v_inst_2201_, v___f_2207_, lean_box(0), lean_box(0), v_it_2203_, v___x_2210_, v___f_2208_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_isEmpty___boxed(lean_object* v_00_u03b1_2212_, lean_object* v_00_u03b2_2213_, lean_object* v_m_2214_, lean_object* v_inst_2215_, lean_object* v_inst_2216_, lean_object* v_inst_2217_, lean_object* v_inst_2218_, lean_object* v_it_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Std_IterM_Total_isEmpty(v_00_u03b1_2212_, v_00_u03b2_2213_, v_m_2214_, v_inst_2215_, v_inst_2216_, v_inst_2217_, v_inst_2218_, v_it_2219_);
lean_dec(v_inst_2216_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg___lam__1(lean_object* v_toPure_2221_, lean_object* v_____do__lift_2222_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = lean_apply_2(v_toPure_2221_, lean_box(0), v_____do__lift_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg___lam__0(lean_object* v_toPure_2224_, lean_object* v_toBind_2225_, lean_object* v___f_2226_, lean_object* v_x1_2227_, lean_object* v_x2_2228_, lean_object* v_x3_2229_){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2230_ = lean_unsigned_to_nat(1u);
v___x_2231_ = lean_nat_add(v_x3_2229_, v___x_2230_);
v___x_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
v___x_2233_ = lean_apply_2(v_toPure_2224_, lean_box(0), v___x_2232_);
v___x_2234_ = lean_apply_4(v_toBind_2225_, lean_box(0), lean_box(0), v___x_2233_, v___f_2226_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg___lam__0___boxed(lean_object* v_toPure_2235_, lean_object* v_toBind_2236_, lean_object* v___f_2237_, lean_object* v_x1_2238_, lean_object* v_x2_2239_, lean_object* v_x3_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Std_IterM_length___redArg___lam__0(v_toPure_2235_, v_toBind_2236_, v___f_2237_, v_x1_2238_, v_x2_2239_, v_x3_2240_);
lean_dec(v_x3_2240_);
lean_dec(v_x1_2238_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg(lean_object* v_inst_2242_, lean_object* v_inst_2243_, lean_object* v_it_2244_){
_start:
{
lean_object* v_toApplicative_2245_; lean_object* v_toBind_2246_; lean_object* v_toPure_2247_; lean_object* v___x_2248_; lean_object* v___f_2249_; lean_object* v___f_2250_; lean_object* v___f_2251_; lean_object* v___x_2252_; 
v_toApplicative_2245_ = lean_ctor_get(v_inst_2243_, 0);
lean_inc_ref(v_toApplicative_2245_);
v_toBind_2246_ = lean_ctor_get(v_inst_2243_, 1);
lean_inc_n(v_toBind_2246_, 2);
lean_dec_ref(v_inst_2243_);
v_toPure_2247_ = lean_ctor_get(v_toApplicative_2245_, 1);
lean_inc_n(v_toPure_2247_, 2);
lean_dec_ref(v_toApplicative_2245_);
v___x_2248_ = lean_unsigned_to_nat(0u);
v___f_2249_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2249_, 0, v_toBind_2246_);
v___f_2250_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2250_, 0, v_toPure_2247_);
v___f_2251_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2251_, 0, v_toPure_2247_);
lean_closure_set(v___f_2251_, 1, v_toBind_2246_);
lean_closure_set(v___f_2251_, 2, v___f_2250_);
v___x_2252_ = lean_apply_6(v_inst_2242_, v___f_2249_, lean_box(0), lean_box(0), v_it_2244_, v___x_2248_, v___f_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length(lean_object* v_00_u03b1_2253_, lean_object* v_m_2254_, lean_object* v_00_u03b2_2255_, lean_object* v_inst_2256_, lean_object* v_inst_2257_, lean_object* v_inst_2258_, lean_object* v_it_2259_){
_start:
{
lean_object* v_toApplicative_2260_; lean_object* v_toBind_2261_; lean_object* v_toPure_2262_; lean_object* v___x_2263_; lean_object* v___f_2264_; lean_object* v___f_2265_; lean_object* v___f_2266_; lean_object* v___x_2267_; 
v_toApplicative_2260_ = lean_ctor_get(v_inst_2258_, 0);
lean_inc_ref(v_toApplicative_2260_);
v_toBind_2261_ = lean_ctor_get(v_inst_2258_, 1);
lean_inc_n(v_toBind_2261_, 2);
lean_dec_ref(v_inst_2258_);
v_toPure_2262_ = lean_ctor_get(v_toApplicative_2260_, 1);
lean_inc_n(v_toPure_2262_, 2);
lean_dec_ref(v_toApplicative_2260_);
v___x_2263_ = lean_unsigned_to_nat(0u);
v___f_2264_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2264_, 0, v_toBind_2261_);
v___f_2265_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2265_, 0, v_toPure_2262_);
v___f_2266_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2266_, 0, v_toPure_2262_);
lean_closure_set(v___f_2266_, 1, v_toBind_2261_);
lean_closure_set(v___f_2266_, 2, v___f_2265_);
v___x_2267_ = lean_apply_6(v_inst_2257_, v___f_2264_, lean_box(0), lean_box(0), v_it_2259_, v___x_2263_, v___f_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___boxed(lean_object* v_00_u03b1_2268_, lean_object* v_m_2269_, lean_object* v_00_u03b2_2270_, lean_object* v_inst_2271_, lean_object* v_inst_2272_, lean_object* v_inst_2273_, lean_object* v_it_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Std_IterM_length(v_00_u03b1_2268_, v_m_2269_, v_00_u03b2_2270_, v_inst_2271_, v_inst_2272_, v_inst_2273_, v_it_2274_);
lean_dec(v_inst_2271_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_count___redArg(lean_object* v_inst_2276_, lean_object* v_inst_2277_, lean_object* v_it_2278_){
_start:
{
lean_object* v_toApplicative_2279_; lean_object* v_toBind_2280_; lean_object* v_toPure_2281_; lean_object* v___x_2282_; lean_object* v___f_2283_; lean_object* v___f_2284_; lean_object* v___f_2285_; lean_object* v___x_2286_; 
v_toApplicative_2279_ = lean_ctor_get(v_inst_2277_, 0);
lean_inc_ref(v_toApplicative_2279_);
v_toBind_2280_ = lean_ctor_get(v_inst_2277_, 1);
lean_inc_n(v_toBind_2280_, 2);
lean_dec_ref(v_inst_2277_);
v_toPure_2281_ = lean_ctor_get(v_toApplicative_2279_, 1);
lean_inc_n(v_toPure_2281_, 2);
lean_dec_ref(v_toApplicative_2279_);
v___x_2282_ = lean_unsigned_to_nat(0u);
v___f_2283_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2283_, 0, v_toBind_2280_);
v___f_2284_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2284_, 0, v_toPure_2281_);
v___f_2285_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2285_, 0, v_toPure_2281_);
lean_closure_set(v___f_2285_, 1, v_toBind_2280_);
lean_closure_set(v___f_2285_, 2, v___f_2284_);
v___x_2286_ = lean_apply_6(v_inst_2276_, v___f_2283_, lean_box(0), lean_box(0), v_it_2278_, v___x_2282_, v___f_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_count(lean_object* v_00_u03b1_2287_, lean_object* v_m_2288_, lean_object* v_00_u03b2_2289_, lean_object* v_inst_2290_, lean_object* v_inst_2291_, lean_object* v_inst_2292_, lean_object* v_it_2293_){
_start:
{
lean_object* v_toApplicative_2294_; lean_object* v_toBind_2295_; lean_object* v_toPure_2296_; lean_object* v___x_2297_; lean_object* v___f_2298_; lean_object* v___f_2299_; lean_object* v___f_2300_; lean_object* v___x_2301_; 
v_toApplicative_2294_ = lean_ctor_get(v_inst_2292_, 0);
lean_inc_ref(v_toApplicative_2294_);
v_toBind_2295_ = lean_ctor_get(v_inst_2292_, 1);
lean_inc_n(v_toBind_2295_, 2);
lean_dec_ref(v_inst_2292_);
v_toPure_2296_ = lean_ctor_get(v_toApplicative_2294_, 1);
lean_inc_n(v_toPure_2296_, 2);
lean_dec_ref(v_toApplicative_2294_);
v___x_2297_ = lean_unsigned_to_nat(0u);
v___f_2298_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2298_, 0, v_toBind_2295_);
v___f_2299_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2299_, 0, v_toPure_2296_);
v___f_2300_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2300_, 0, v_toPure_2296_);
lean_closure_set(v___f_2300_, 1, v_toBind_2295_);
lean_closure_set(v___f_2300_, 2, v___f_2299_);
v___x_2301_ = lean_apply_6(v_inst_2291_, v___f_2298_, lean_box(0), lean_box(0), v_it_2293_, v___x_2297_, v___f_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_count___boxed(lean_object* v_00_u03b1_2302_, lean_object* v_m_2303_, lean_object* v_00_u03b2_2304_, lean_object* v_inst_2305_, lean_object* v_inst_2306_, lean_object* v_inst_2307_, lean_object* v_it_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Std_IterM_count(v_00_u03b1_2302_, v_m_2303_, v_00_u03b2_2304_, v_inst_2305_, v_inst_2306_, v_inst_2307_, v_it_2308_);
lean_dec(v_inst_2305_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_size___redArg(lean_object* v_inst_2310_, lean_object* v_inst_2311_, lean_object* v_it_2312_){
_start:
{
lean_object* v_toApplicative_2313_; lean_object* v_toBind_2314_; lean_object* v_toPure_2315_; lean_object* v___x_2316_; lean_object* v___f_2317_; lean_object* v___f_2318_; lean_object* v___f_2319_; lean_object* v___x_2320_; 
v_toApplicative_2313_ = lean_ctor_get(v_inst_2311_, 0);
lean_inc_ref(v_toApplicative_2313_);
v_toBind_2314_ = lean_ctor_get(v_inst_2311_, 1);
lean_inc_n(v_toBind_2314_, 2);
lean_dec_ref(v_inst_2311_);
v_toPure_2315_ = lean_ctor_get(v_toApplicative_2313_, 1);
lean_inc_n(v_toPure_2315_, 2);
lean_dec_ref(v_toApplicative_2313_);
v___x_2316_ = lean_unsigned_to_nat(0u);
v___f_2317_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2317_, 0, v_toBind_2314_);
v___f_2318_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2318_, 0, v_toPure_2315_);
v___f_2319_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2319_, 0, v_toPure_2315_);
lean_closure_set(v___f_2319_, 1, v_toBind_2314_);
lean_closure_set(v___f_2319_, 2, v___f_2318_);
v___x_2320_ = lean_apply_6(v_inst_2310_, v___f_2317_, lean_box(0), lean_box(0), v_it_2312_, v___x_2316_, v___f_2319_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_size(lean_object* v_00_u03b1_2321_, lean_object* v_m_2322_, lean_object* v_00_u03b2_2323_, lean_object* v_inst_2324_, lean_object* v_inst_2325_, lean_object* v_inst_2326_, lean_object* v_it_2327_){
_start:
{
lean_object* v_toApplicative_2328_; lean_object* v_toBind_2329_; lean_object* v_toPure_2330_; lean_object* v___x_2331_; lean_object* v___f_2332_; lean_object* v___f_2333_; lean_object* v___f_2334_; lean_object* v___x_2335_; 
v_toApplicative_2328_ = lean_ctor_get(v_inst_2326_, 0);
lean_inc_ref(v_toApplicative_2328_);
v_toBind_2329_ = lean_ctor_get(v_inst_2326_, 1);
lean_inc_n(v_toBind_2329_, 2);
lean_dec_ref(v_inst_2326_);
v_toPure_2330_ = lean_ctor_get(v_toApplicative_2328_, 1);
lean_inc_n(v_toPure_2330_, 2);
lean_dec_ref(v_toApplicative_2328_);
v___x_2331_ = lean_unsigned_to_nat(0u);
v___f_2332_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2332_, 0, v_toBind_2329_);
v___f_2333_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2333_, 0, v_toPure_2330_);
v___f_2334_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2334_, 0, v_toPure_2330_);
lean_closure_set(v___f_2334_, 1, v_toBind_2329_);
lean_closure_set(v___f_2334_, 2, v___f_2333_);
v___x_2335_ = lean_apply_6(v_inst_2325_, v___f_2332_, lean_box(0), lean_box(0), v_it_2327_, v___x_2331_, v___f_2334_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_size___boxed(lean_object* v_00_u03b1_2336_, lean_object* v_m_2337_, lean_object* v_00_u03b2_2338_, lean_object* v_inst_2339_, lean_object* v_inst_2340_, lean_object* v_inst_2341_, lean_object* v_it_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Std_IterM_size(v_00_u03b1_2336_, v_m_2337_, v_00_u03b2_2338_, v_inst_2339_, v_inst_2340_, v_inst_2341_, v_it_2342_);
lean_dec(v_inst_2339_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count___redArg(lean_object* v_inst_2344_, lean_object* v_inst_2345_, lean_object* v_it_2346_){
_start:
{
lean_object* v_toApplicative_2347_; lean_object* v_toBind_2348_; lean_object* v_toPure_2349_; lean_object* v___x_2350_; lean_object* v___f_2351_; lean_object* v___f_2352_; lean_object* v___f_2353_; lean_object* v___x_2354_; 
v_toApplicative_2347_ = lean_ctor_get(v_inst_2345_, 0);
lean_inc_ref(v_toApplicative_2347_);
v_toBind_2348_ = lean_ctor_get(v_inst_2345_, 1);
lean_inc_n(v_toBind_2348_, 2);
lean_dec_ref(v_inst_2345_);
v_toPure_2349_ = lean_ctor_get(v_toApplicative_2347_, 1);
lean_inc_n(v_toPure_2349_, 2);
lean_dec_ref(v_toApplicative_2347_);
v___x_2350_ = lean_unsigned_to_nat(0u);
v___f_2351_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2351_, 0, v_toBind_2348_);
v___f_2352_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2352_, 0, v_toPure_2349_);
v___f_2353_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2353_, 0, v_toPure_2349_);
lean_closure_set(v___f_2353_, 1, v_toBind_2348_);
lean_closure_set(v___f_2353_, 2, v___f_2352_);
v___x_2354_ = lean_apply_6(v_inst_2344_, v___f_2351_, lean_box(0), lean_box(0), v_it_2346_, v___x_2350_, v___f_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count(lean_object* v_00_u03b1_2355_, lean_object* v_m_2356_, lean_object* v_00_u03b2_2357_, lean_object* v_inst_2358_, lean_object* v_inst_2359_, lean_object* v_inst_2360_, lean_object* v_it_2361_){
_start:
{
lean_object* v_toApplicative_2362_; lean_object* v_toBind_2363_; lean_object* v_toPure_2364_; lean_object* v___x_2365_; lean_object* v___f_2366_; lean_object* v___f_2367_; lean_object* v___f_2368_; lean_object* v___x_2369_; 
v_toApplicative_2362_ = lean_ctor_get(v_inst_2360_, 0);
lean_inc_ref(v_toApplicative_2362_);
v_toBind_2363_ = lean_ctor_get(v_inst_2360_, 1);
lean_inc_n(v_toBind_2363_, 2);
lean_dec_ref(v_inst_2360_);
v_toPure_2364_ = lean_ctor_get(v_toApplicative_2362_, 1);
lean_inc_n(v_toPure_2364_, 2);
lean_dec_ref(v_toApplicative_2362_);
v___x_2365_ = lean_unsigned_to_nat(0u);
v___f_2366_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2366_, 0, v_toBind_2363_);
v___f_2367_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2367_, 0, v_toPure_2364_);
v___f_2368_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2368_, 0, v_toPure_2364_);
lean_closure_set(v___f_2368_, 1, v_toBind_2363_);
lean_closure_set(v___f_2368_, 2, v___f_2367_);
v___x_2369_ = lean_apply_6(v_inst_2359_, v___f_2366_, lean_box(0), lean_box(0), v_it_2361_, v___x_2365_, v___f_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count___boxed(lean_object* v_00_u03b1_2370_, lean_object* v_m_2371_, lean_object* v_00_u03b2_2372_, lean_object* v_inst_2373_, lean_object* v_inst_2374_, lean_object* v_inst_2375_, lean_object* v_it_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Std_IterM_Partial_count(v_00_u03b1_2370_, v_m_2371_, v_00_u03b2_2372_, v_inst_2373_, v_inst_2374_, v_inst_2375_, v_it_2376_);
lean_dec(v_inst_2373_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size___redArg(lean_object* v_inst_2378_, lean_object* v_inst_2379_, lean_object* v_it_2380_){
_start:
{
lean_object* v_toApplicative_2381_; lean_object* v_toBind_2382_; lean_object* v_toPure_2383_; lean_object* v___x_2384_; lean_object* v___f_2385_; lean_object* v___f_2386_; lean_object* v___f_2387_; lean_object* v___x_2388_; 
v_toApplicative_2381_ = lean_ctor_get(v_inst_2379_, 0);
lean_inc_ref(v_toApplicative_2381_);
v_toBind_2382_ = lean_ctor_get(v_inst_2379_, 1);
lean_inc_n(v_toBind_2382_, 2);
lean_dec_ref(v_inst_2379_);
v_toPure_2383_ = lean_ctor_get(v_toApplicative_2381_, 1);
lean_inc_n(v_toPure_2383_, 2);
lean_dec_ref(v_toApplicative_2381_);
v___x_2384_ = lean_unsigned_to_nat(0u);
v___f_2385_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2385_, 0, v_toBind_2382_);
v___f_2386_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2386_, 0, v_toPure_2383_);
v___f_2387_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2387_, 0, v_toPure_2383_);
lean_closure_set(v___f_2387_, 1, v_toBind_2382_);
lean_closure_set(v___f_2387_, 2, v___f_2386_);
v___x_2388_ = lean_apply_6(v_inst_2378_, v___f_2385_, lean_box(0), lean_box(0), v_it_2380_, v___x_2384_, v___f_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size(lean_object* v_00_u03b1_2389_, lean_object* v_m_2390_, lean_object* v_00_u03b2_2391_, lean_object* v_inst_2392_, lean_object* v_inst_2393_, lean_object* v_inst_2394_, lean_object* v_it_2395_){
_start:
{
lean_object* v_toApplicative_2396_; lean_object* v_toBind_2397_; lean_object* v_toPure_2398_; lean_object* v___x_2399_; lean_object* v___f_2400_; lean_object* v___f_2401_; lean_object* v___f_2402_; lean_object* v___x_2403_; 
v_toApplicative_2396_ = lean_ctor_get(v_inst_2394_, 0);
lean_inc_ref(v_toApplicative_2396_);
v_toBind_2397_ = lean_ctor_get(v_inst_2394_, 1);
lean_inc_n(v_toBind_2397_, 2);
lean_dec_ref(v_inst_2394_);
v_toPure_2398_ = lean_ctor_get(v_toApplicative_2396_, 1);
lean_inc_n(v_toPure_2398_, 2);
lean_dec_ref(v_toApplicative_2396_);
v___x_2399_ = lean_unsigned_to_nat(0u);
v___f_2400_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2400_, 0, v_toBind_2397_);
v___f_2401_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2401_, 0, v_toPure_2398_);
v___f_2402_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2402_, 0, v_toPure_2398_);
lean_closure_set(v___f_2402_, 1, v_toBind_2397_);
lean_closure_set(v___f_2402_, 2, v___f_2401_);
v___x_2403_ = lean_apply_6(v_inst_2393_, v___f_2400_, lean_box(0), lean_box(0), v_it_2395_, v___x_2399_, v___f_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size___boxed(lean_object* v_00_u03b1_2404_, lean_object* v_m_2405_, lean_object* v_00_u03b2_2406_, lean_object* v_inst_2407_, lean_object* v_inst_2408_, lean_object* v_inst_2409_, lean_object* v_it_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Std_IterM_Partial_size(v_00_u03b1_2404_, v_m_2405_, v_00_u03b2_2406_, v_inst_2407_, v_inst_2408_, v_inst_2409_, v_it_2410_);
lean_dec(v_inst_2407_);
return v_res_2411_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Partial(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(uint8_t builtin);
lean_object* runtime_initialize_Init_WFExtrinsicFix(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
