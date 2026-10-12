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
lean_object* l_Std_IteratorLoop_WithWF_instWellFoundedRelation___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l_Std_IteratorLoop_WithWF_instWellFoundedRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_Std_IteratorLoop_WithWF_instWellFoundedRelation___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_WithWF_instWellFoundedRelation___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Std_IteratorLoop_WithWF_instWellFoundedRelation___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_WithWF_instWellFoundedRelation(lean_object* v_00_u03b1_6_, lean_object* v_m_7_, lean_object* v_00_u03b2_8_, lean_object* v_inst_9_, lean_object* v_00_u03b3_10_, lean_object* v_PlausibleForInStep_11_, lean_object* v_hwf_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_box(0);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_WithWF_instWellFoundedRelation___boxed(lean_object* v_00_u03b1_14_, lean_object* v_m_15_, lean_object* v_00_u03b2_16_, lean_object* v_inst_17_, lean_object* v_00_u03b3_18_, lean_object* v_PlausibleForInStep_19_, lean_object* v_hwf_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Std_IteratorLoop_WithWF_instWellFoundedRelation(v_00_u03b1_14_, v_m_15_, v_00_u03b2_16_, v_inst_17_, v_00_u03b3_18_, v_PlausibleForInStep_19_, v_hwf_20_);
lean_dec(v_inst_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0(lean_object* v_toPure_22_, lean_object* v_recur_23_, lean_object* v_it_24_, lean_object* v_____do__lift_25_){
_start:
{
if (lean_obj_tag(v_____do__lift_25_) == 0)
{
lean_object* v_a_26_; lean_object* v___x_27_; 
lean_dec(v_it_24_);
lean_dec(v_recur_23_);
v_a_26_ = lean_ctor_get(v_____do__lift_25_, 0);
lean_inc(v_a_26_);
lean_dec_ref_known(v_____do__lift_25_, 1);
v___x_27_ = lean_apply_2(v_toPure_22_, lean_box(0), v_a_26_);
return v___x_27_;
}
else
{
lean_object* v_a_28_; lean_object* v___x_29_; 
lean_dec(v_toPure_22_);
v_a_28_ = lean_ctor_get(v_____do__lift_25_, 0);
lean_inc(v_a_28_);
lean_dec_ref_known(v_____do__lift_25_, 1);
v___x_29_ = lean_apply_4(v_recur_23_, v_it_24_, v_a_28_, lean_box(0), lean_box(0));
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__1(lean_object* v_toPure_30_, lean_object* v_recur_31_, lean_object* v_f_32_, lean_object* v_acc_33_, lean_object* v_toBind_34_, lean_object* v_s_35_){
_start:
{
switch(lean_obj_tag(v_s_35_))
{
case 0:
{
lean_object* v_it_36_; lean_object* v_out_37_; lean_object* v___f_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v_it_36_ = lean_ctor_get(v_s_35_, 0);
lean_inc(v_it_36_);
v_out_37_ = lean_ctor_get(v_s_35_, 1);
lean_inc(v_out_37_);
lean_dec_ref_known(v_s_35_, 2);
v___f_38_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_38_, 0, v_toPure_30_);
lean_closure_set(v___f_38_, 1, v_recur_31_);
lean_closure_set(v___f_38_, 2, v_it_36_);
v___x_39_ = lean_apply_3(v_f_32_, v_out_37_, lean_box(0), v_acc_33_);
v___x_40_ = lean_apply_4(v_toBind_34_, lean_box(0), lean_box(0), v___x_39_, v___f_38_);
return v___x_40_;
}
case 1:
{
lean_object* v_it_41_; lean_object* v___x_42_; 
lean_dec(v_toBind_34_);
lean_dec(v_f_32_);
lean_dec(v_toPure_30_);
v_it_41_ = lean_ctor_get(v_s_35_, 0);
lean_inc(v_it_41_);
lean_dec_ref_known(v_s_35_, 1);
v___x_42_ = lean_apply_4(v_recur_31_, v_it_41_, v_acc_33_, lean_box(0), lean_box(0));
return v___x_42_;
}
default: 
{
lean_object* v___x_43_; 
lean_dec(v_toBind_34_);
lean_dec(v_f_32_);
lean_dec(v_recur_31_);
v___x_43_ = lean_apply_2(v_toPure_30_, lean_box(0), v_acc_33_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2(lean_object* v_toPure_44_, lean_object* v_f_45_, lean_object* v_toBind_46_, lean_object* v_inst_47_, lean_object* v_lift_48_, lean_object* v_it_49_, lean_object* v_acc_50_, lean_object* v_hP_51_, lean_object* v_recur_52_){
_start:
{
lean_object* v___f_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___f_53_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__1), 6, 5);
lean_closure_set(v___f_53_, 0, v_toPure_44_);
lean_closure_set(v___f_53_, 1, v_recur_52_);
lean_closure_set(v___f_53_, 2, v_f_45_);
lean_closure_set(v___f_53_, 3, v_acc_50_);
lean_closure_set(v___f_53_, 4, v_toBind_46_);
v___x_54_ = lean_apply_1(v_inst_47_, v_it_49_);
v___x_55_ = lean_apply_4(v_lift_48_, lean_box(0), lean_box(0), v___f_53_, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27___redArg(lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_lift_58_, lean_object* v_it_59_, lean_object* v_init_60_, lean_object* v_f_61_){
_start:
{
lean_object* v_toApplicative_62_; lean_object* v_toBind_63_; lean_object* v_toPure_64_; lean_object* v___f_65_; lean_object* v___x_66_; 
v_toApplicative_62_ = lean_ctor_get(v_inst_57_, 0);
lean_inc_ref(v_toApplicative_62_);
v_toBind_63_ = lean_ctor_get(v_inst_57_, 1);
lean_inc(v_toBind_63_);
lean_dec_ref(v_inst_57_);
v_toPure_64_ = lean_ctor_get(v_toApplicative_62_, 1);
lean_inc(v_toPure_64_);
lean_dec_ref(v_toApplicative_62_);
v___f_65_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2), 9, 5);
lean_closure_set(v___f_65_, 0, v_toPure_64_);
lean_closure_set(v___f_65_, 1, v_f_61_);
lean_closure_set(v___f_65_, 2, v_toBind_63_);
lean_closure_set(v___f_65_, 3, v_inst_56_);
lean_closure_set(v___f_65_, 4, v_lift_58_);
v___x_66_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_65_, v_it_59_, v_init_60_, lean_box(0));
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27(lean_object* v_m_67_, lean_object* v_00_u03b1_68_, lean_object* v_00_u03b2_69_, lean_object* v_inst_70_, lean_object* v_n_71_, lean_object* v_inst_72_, lean_object* v_lift_73_, lean_object* v_00_u03b3_74_, lean_object* v_PlausibleForInStep_75_, lean_object* v_it_76_, lean_object* v_init_77_, lean_object* v_P_78_, lean_object* v_hP_79_, lean_object* v_f_80_){
_start:
{
lean_object* v_toApplicative_81_; lean_object* v_toBind_82_; lean_object* v_toPure_83_; lean_object* v___f_84_; lean_object* v___x_85_; 
v_toApplicative_81_ = lean_ctor_get(v_inst_72_, 0);
lean_inc_ref(v_toApplicative_81_);
v_toBind_82_ = lean_ctor_get(v_inst_72_, 1);
lean_inc(v_toBind_82_);
lean_dec_ref(v_inst_72_);
v_toPure_83_ = lean_ctor_get(v_toApplicative_81_, 1);
lean_inc(v_toPure_83_);
lean_dec_ref(v_toApplicative_81_);
v___f_84_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__2), 9, 5);
lean_closure_set(v___f_84_, 0, v_toPure_83_);
lean_closure_set(v___f_84_, 1, v_f_80_);
lean_closure_set(v___f_84_, 2, v_toBind_82_);
lean_closure_set(v___f_84_, 3, v_inst_70_);
lean_closure_set(v___f_84_, 4, v_lift_73_);
v___x_85_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_84_, v_it_76_, v_init_77_, lean_box(0));
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__1(lean_object* v_toPure_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_lift_89_, lean_object* v_f_90_, lean_object* v_init_91_, lean_object* v_toBind_92_, lean_object* v_s_93_){
_start:
{
switch(lean_obj_tag(v_s_93_))
{
case 0:
{
lean_object* v_it_94_; lean_object* v_out_95_; lean_object* v___f_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v_it_94_ = lean_ctor_get(v_s_93_, 0);
lean_inc(v_it_94_);
v_out_95_ = lean_ctor_get(v_s_93_, 1);
lean_inc(v_out_95_);
lean_dec_ref_known(v_s_93_, 2);
lean_inc(v_f_90_);
v___f_96_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__0), 7, 6);
lean_closure_set(v___f_96_, 0, v_toPure_86_);
lean_closure_set(v___f_96_, 1, v_inst_87_);
lean_closure_set(v___f_96_, 2, v_inst_88_);
lean_closure_set(v___f_96_, 3, v_lift_89_);
lean_closure_set(v___f_96_, 4, v_it_94_);
lean_closure_set(v___f_96_, 5, v_f_90_);
v___x_97_ = lean_apply_3(v_f_90_, v_out_95_, lean_box(0), v_init_91_);
v___x_98_ = lean_apply_4(v_toBind_92_, lean_box(0), lean_box(0), v___x_97_, v___f_96_);
return v___x_98_;
}
case 1:
{
lean_object* v_it_99_; lean_object* v___x_100_; 
lean_dec(v_toBind_92_);
lean_dec(v_toPure_86_);
v_it_99_ = lean_ctor_get(v_s_93_, 0);
lean_inc(v_it_99_);
lean_dec_ref_known(v_s_93_, 1);
v___x_100_ = l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(v_inst_87_, v_inst_88_, v_lift_89_, v_it_99_, v_init_91_, v_f_90_);
return v___x_100_;
}
default: 
{
lean_object* v___x_101_; 
lean_dec(v_toBind_92_);
lean_dec(v_f_90_);
lean_dec(v_lift_89_);
lean_dec_ref(v_inst_88_);
lean_dec(v_inst_87_);
v___x_101_ = lean_apply_2(v_toPure_86_, lean_box(0), v_init_91_);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_lift_104_, lean_object* v_it_105_, lean_object* v_init_106_, lean_object* v_f_107_){
_start:
{
lean_object* v_toApplicative_108_; lean_object* v_toBind_109_; lean_object* v_toPure_110_; lean_object* v___f_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_toApplicative_108_ = lean_ctor_get(v_inst_103_, 0);
v_toBind_109_ = lean_ctor_get(v_inst_103_, 1);
lean_inc(v_toBind_109_);
v_toPure_110_ = lean_ctor_get(v_toApplicative_108_, 1);
lean_inc(v_toPure_110_);
lean_inc(v_lift_104_);
lean_inc(v_inst_102_);
v___f_111_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__1), 8, 7);
lean_closure_set(v___f_111_, 0, v_toPure_110_);
lean_closure_set(v___f_111_, 1, v_inst_102_);
lean_closure_set(v___f_111_, 2, v_inst_103_);
lean_closure_set(v___f_111_, 3, v_lift_104_);
lean_closure_set(v___f_111_, 4, v_f_107_);
lean_closure_set(v___f_111_, 5, v_init_106_);
lean_closure_set(v___f_111_, 6, v_toBind_109_);
v___x_112_ = lean_apply_1(v_inst_102_, v_it_105_);
v___x_113_ = lean_apply_4(v_lift_104_, lean_box(0), lean_box(0), v___f_111_, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg___lam__0(lean_object* v_toPure_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_lift_117_, lean_object* v_it_118_, lean_object* v_f_119_, lean_object* v_____do__lift_120_){
_start:
{
if (lean_obj_tag(v_____do__lift_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_122_; 
lean_dec(v_f_119_);
lean_dec(v_it_118_);
lean_dec(v_lift_117_);
lean_dec_ref(v_inst_116_);
lean_dec(v_inst_115_);
v_a_121_ = lean_ctor_get(v_____do__lift_120_, 0);
lean_inc(v_a_121_);
lean_dec_ref_known(v_____do__lift_120_, 1);
v___x_122_ = lean_apply_2(v_toPure_114_, lean_box(0), v_a_121_);
return v___x_122_;
}
else
{
lean_object* v_a_123_; lean_object* v___x_124_; 
lean_dec(v_toPure_114_);
v_a_123_ = lean_ctor_get(v_____do__lift_120_, 0);
lean_inc(v_a_123_);
lean_dec_ref_known(v_____do__lift_120_, 1);
v___x_124_ = l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(v_inst_115_, v_inst_116_, v_lift_117_, v_it_118_, v_a_123_, v_f_119_);
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_DefaultConsumers_forIn_x27_wf(lean_object* v_m_125_, lean_object* v_00_u03b1_126_, lean_object* v_00_u03b2_127_, lean_object* v_inst_128_, lean_object* v_n_129_, lean_object* v_inst_130_, lean_object* v_lift_131_, lean_object* v_00_u03b3_132_, lean_object* v_PlausibleForInStep_133_, lean_object* v_wf_134_, lean_object* v_it_135_, lean_object* v_init_136_, lean_object* v_P_137_, lean_object* v_hP_138_, lean_object* v_f_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Std_IterM_DefaultConsumers_forIn_x27_wf___redArg(v_inst_128_, v_inst_130_, v_lift_131_, v_it_135_, v_init_136_, v_f_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(lean_object* v_x_141_, lean_object* v_h__1_142_, lean_object* v_h__2_143_, lean_object* v_h__3_144_){
_start:
{
switch(lean_obj_tag(v_x_141_))
{
case 0:
{
lean_object* v_it_145_; lean_object* v_out_146_; lean_object* v___x_147_; 
lean_dec(v_h__3_144_);
lean_dec(v_h__2_143_);
v_it_145_ = lean_ctor_get(v_x_141_, 0);
lean_inc(v_it_145_);
v_out_146_ = lean_ctor_get(v_x_141_, 1);
lean_inc(v_out_146_);
lean_dec_ref_known(v_x_141_, 2);
v___x_147_ = lean_apply_3(v_h__1_142_, v_it_145_, v_out_146_, lean_box(0));
return v___x_147_;
}
case 1:
{
lean_object* v_it_148_; lean_object* v___x_149_; 
lean_dec(v_h__3_144_);
lean_dec(v_h__1_142_);
v_it_148_ = lean_ctor_get(v_x_141_, 0);
lean_inc(v_it_148_);
lean_dec_ref_known(v_x_141_, 1);
v___x_149_ = lean_apply_2(v_h__2_143_, v_it_148_, lean_box(0));
return v___x_149_;
}
default: 
{
lean_object* v___x_150_; 
lean_dec(v_h__2_143_);
lean_dec(v_h__1_142_);
v___x_150_ = lean_apply_1(v_h__3_144_, lean_box(0));
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(lean_object* v_m_151_, lean_object* v_00_u03b1_152_, lean_object* v_00_u03b2_153_, lean_object* v_inst_154_, lean_object* v_it_155_, lean_object* v_motive_156_, lean_object* v_x_157_, lean_object* v_h__1_158_, lean_object* v_h__2_159_, lean_object* v_h__3_160_){
_start:
{
switch(lean_obj_tag(v_x_157_))
{
case 0:
{
lean_object* v_it_161_; lean_object* v_out_162_; lean_object* v___x_163_; 
lean_dec(v_h__3_160_);
lean_dec(v_h__2_159_);
v_it_161_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_it_161_);
v_out_162_ = lean_ctor_get(v_x_157_, 1);
lean_inc(v_out_162_);
lean_dec_ref_known(v_x_157_, 2);
v___x_163_ = lean_apply_3(v_h__1_158_, v_it_161_, v_out_162_, lean_box(0));
return v___x_163_;
}
case 1:
{
lean_object* v_it_164_; lean_object* v___x_165_; 
lean_dec(v_h__3_160_);
lean_dec(v_h__1_158_);
v_it_164_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_it_164_);
lean_dec_ref_known(v_x_157_, 1);
v___x_165_ = lean_apply_2(v_h__2_159_, v_it_164_, lean_box(0));
return v___x_165_;
}
default: 
{
lean_object* v___x_166_; 
lean_dec(v_h__2_159_);
lean_dec(v_h__1_158_);
v___x_166_ = lean_apply_1(v_h__3_160_, lean_box(0));
return v___x_166_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(lean_object* v_m_167_, lean_object* v_00_u03b1_168_, lean_object* v_00_u03b2_169_, lean_object* v_inst_170_, lean_object* v_it_171_, lean_object* v_motive_172_, lean_object* v_x_173_, lean_object* v_h__1_174_, lean_object* v_h__2_175_, lean_object* v_h__3_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(v_m_167_, v_00_u03b1_168_, v_00_u03b2_169_, v_inst_170_, v_it_171_, v_motive_172_, v_x_173_, v_h__1_174_, v_h__2_175_, v_h__3_176_);
lean_dec(v_it_171_);
lean_dec(v_inst_170_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(lean_object* v_____do__lift_178_, lean_object* v_h__1_179_, lean_object* v_h__2_180_){
_start:
{
if (lean_obj_tag(v_____do__lift_178_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_182_; 
lean_dec(v_h__1_179_);
v_a_181_ = lean_ctor_get(v_____do__lift_178_, 0);
lean_inc(v_a_181_);
lean_dec_ref_known(v_____do__lift_178_, 1);
v___x_182_ = lean_apply_2(v_h__2_180_, v_a_181_, lean_box(0));
return v___x_182_;
}
else
{
lean_object* v_a_183_; lean_object* v___x_184_; 
lean_dec(v_h__2_180_);
v_a_183_ = lean_ctor_get(v_____do__lift_178_, 0);
lean_inc(v_a_183_);
lean_dec_ref_known(v_____do__lift_178_, 1);
v___x_184_ = lean_apply_2(v_h__1_179_, v_a_183_, lean_box(0));
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(lean_object* v_00_u03b2_185_, lean_object* v_00_u03b3_186_, lean_object* v_PlausibleForInStep_187_, lean_object* v_acc_188_, lean_object* v_out_189_, lean_object* v_motive_190_, lean_object* v_____do__lift_191_, lean_object* v_h__1_192_, lean_object* v_h__2_193_){
_start:
{
if (lean_obj_tag(v_____do__lift_191_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_195_; 
lean_dec(v_h__1_192_);
v_a_194_ = lean_ctor_get(v_____do__lift_191_, 0);
lean_inc(v_a_194_);
lean_dec_ref_known(v_____do__lift_191_, 1);
v___x_195_ = lean_apply_2(v_h__2_193_, v_a_194_, lean_box(0));
return v___x_195_;
}
else
{
lean_object* v_a_196_; lean_object* v___x_197_; 
lean_dec(v_h__2_193_);
v_a_196_ = lean_ctor_get(v_____do__lift_191_, 0);
lean_inc(v_a_196_);
lean_dec_ref_known(v_____do__lift_191_, 1);
v___x_197_ = lean_apply_2(v_h__1_192_, v_a_196_, lean_box(0));
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(lean_object* v_00_u03b2_198_, lean_object* v_00_u03b3_199_, lean_object* v_PlausibleForInStep_200_, lean_object* v_acc_201_, lean_object* v_out_202_, lean_object* v_motive_203_, lean_object* v_____do__lift_204_, lean_object* v_h__1_205_, lean_object* v_h__2_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Init_Data_Iterators_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(v_00_u03b2_198_, v_00_u03b3_199_, v_PlausibleForInStep_200_, v_acc_201_, v_out_202_, v_motive_203_, v_____do__lift_204_, v_h__1_205_, v_h__2_206_);
lean_dec(v_out_202_);
lean_dec(v_acc_201_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__1(lean_object* v_toPure_208_, lean_object* v_recur_209_, lean_object* v___y_210_, lean_object* v_acc_211_, lean_object* v_toBind_212_, lean_object* v_s_213_){
_start:
{
switch(lean_obj_tag(v_s_213_))
{
case 0:
{
lean_object* v_it_214_; lean_object* v_out_215_; lean_object* v___f_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_it_214_ = lean_ctor_get(v_s_213_, 0);
lean_inc(v_it_214_);
v_out_215_ = lean_ctor_get(v_s_213_, 1);
lean_inc(v_out_215_);
lean_dec_ref_known(v_s_213_, 2);
v___f_216_ = lean_alloc_closure((void*)(l_Std_IterM_DefaultConsumers_forIn_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_216_, 0, v_toPure_208_);
lean_closure_set(v___f_216_, 1, v_recur_209_);
lean_closure_set(v___f_216_, 2, v_it_214_);
v___x_217_ = lean_apply_3(v___y_210_, v_out_215_, lean_box(0), v_acc_211_);
v___x_218_ = lean_apply_4(v_toBind_212_, lean_box(0), lean_box(0), v___x_217_, v___f_216_);
return v___x_218_;
}
case 1:
{
lean_object* v_it_219_; lean_object* v___x_220_; 
lean_dec(v_toBind_212_);
lean_dec(v___y_210_);
lean_dec(v_toPure_208_);
v_it_219_ = lean_ctor_get(v_s_213_, 0);
lean_inc(v_it_219_);
lean_dec_ref_known(v_s_213_, 1);
v___x_220_ = lean_apply_4(v_recur_209_, v_it_219_, v_acc_211_, lean_box(0), lean_box(0));
return v___x_220_;
}
default: 
{
lean_object* v___x_221_; 
lean_dec(v_toBind_212_);
lean_dec(v___y_210_);
lean_dec(v_recur_209_);
v___x_221_ = lean_apply_2(v_toPure_208_, lean_box(0), v_acc_211_);
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__0(lean_object* v_toPure_222_, lean_object* v___y_223_, lean_object* v_toBind_224_, lean_object* v_inst_225_, lean_object* v_lift_226_, lean_object* v_it_227_, lean_object* v_acc_228_, lean_object* v_hP_229_, lean_object* v_recur_230_){
_start:
{
lean_object* v___f_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___f_231_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__1), 6, 5);
lean_closure_set(v___f_231_, 0, v_toPure_222_);
lean_closure_set(v___f_231_, 1, v_recur_230_);
lean_closure_set(v___f_231_, 2, v___y_223_);
lean_closure_set(v___f_231_, 3, v_acc_228_);
lean_closure_set(v___f_231_, 4, v_toBind_224_);
v___x_232_ = lean_apply_1(v_inst_225_, v_it_227_);
v___x_233_ = lean_apply_4(v_lift_226_, lean_box(0), lean_box(0), v___f_231_, v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg___lam__2(lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_lift_236_, lean_object* v_00_u03b3_237_, lean_object* v_Pl_238_, lean_object* v_it_239_, lean_object* v_init_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_toApplicative_242_; lean_object* v_toBind_243_; lean_object* v_toPure_244_; lean_object* v___f_245_; lean_object* v___x_246_; 
v_toApplicative_242_ = lean_ctor_get(v_inst_234_, 0);
lean_inc_ref(v_toApplicative_242_);
v_toBind_243_ = lean_ctor_get(v_inst_234_, 1);
lean_inc(v_toBind_243_);
lean_dec_ref(v_inst_234_);
v_toPure_244_ = lean_ctor_get(v_toApplicative_242_, 1);
lean_inc(v_toPure_244_);
lean_dec_ref(v_toApplicative_242_);
v___f_245_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__0), 9, 5);
lean_closure_set(v___f_245_, 0, v_toPure_244_);
lean_closure_set(v___f_245_, 1, v___y_241_);
lean_closure_set(v___f_245_, 2, v_toBind_243_);
lean_closure_set(v___f_245_, 3, v_inst_235_);
lean_closure_set(v___f_245_, 4, v_lift_236_);
v___x_246_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_245_, v_it_239_, v_init_240_, lean_box(0));
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation___redArg(lean_object* v_inst_247_, lean_object* v_inst_248_){
_start:
{
lean_object* v___f_249_; 
v___f_249_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__2), 8, 2);
lean_closure_set(v___f_249_, 0, v_inst_247_);
lean_closure_set(v___f_249_, 1, v_inst_248_);
return v___f_249_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_defaultImplementation(lean_object* v_00_u03b2_250_, lean_object* v_00_u03b1_251_, lean_object* v_m_252_, lean_object* v_n_253_, lean_object* v_inst_254_, lean_object* v_inst_255_){
_start:
{
lean_object* v___f_256_; 
v___f_256_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_defaultImplementation___redArg___lam__2), 8, 2);
lean_closure_set(v___f_256_, 0, v_inst_254_);
lean_closure_set(v___f_256_, 1, v_inst_255_);
return v___f_256_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0(lean_object* v_toPure_257_, lean_object* v_____do__lift_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = lean_apply_2(v_toPure_257_, lean_box(0), v_____do__lift_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1(lean_object* v_f_260_, lean_object* v_toBind_261_, lean_object* v___f_262_, lean_object* v_x1_263_, lean_object* v_x2_264_, lean_object* v_x3_265_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_apply_3(v_f_260_, v_x1_263_, lean_box(0), v_x3_265_);
v___x_267_ = lean_apply_4(v_toBind_261_, lean_box(0), lean_box(0), v___x_266_, v___f_262_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2(lean_object* v_toBind_268_, lean_object* v___f_269_, lean_object* v_inst_270_, lean_object* v_lift_271_, lean_object* v_00_u03b3_272_, lean_object* v_it_273_, lean_object* v_init_274_, lean_object* v_f_275_){
_start:
{
lean_object* v___f_276_; lean_object* v___x_277_; 
v___f_276_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1), 6, 3);
lean_closure_set(v___f_276_, 0, v_f_275_);
lean_closure_set(v___f_276_, 1, v_toBind_268_);
lean_closure_set(v___f_276_, 2, v___f_269_);
v___x_277_ = lean_apply_6(v_inst_270_, v_lift_271_, lean_box(0), lean_box(0), v_it_273_, v_init_274_, v___f_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___redArg(lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_lift_280_){
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
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27(lean_object* v_m_286_, lean_object* v_n_287_, lean_object* v_00_u03b1_288_, lean_object* v_00_u03b2_289_, lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_lift_293_){
_start:
{
lean_object* v_toApplicative_294_; lean_object* v_toBind_295_; lean_object* v_toPure_296_; lean_object* v___f_297_; lean_object* v___f_298_; 
v_toApplicative_294_ = lean_ctor_get(v_inst_292_, 0);
lean_inc_ref(v_toApplicative_294_);
v_toBind_295_ = lean_ctor_get(v_inst_292_, 1);
lean_inc(v_toBind_295_);
lean_dec_ref(v_inst_292_);
v_toPure_296_ = lean_ctor_get(v_toApplicative_294_, 1);
lean_inc(v_toPure_296_);
lean_dec_ref(v_toApplicative_294_);
v___f_297_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_297_, 0, v_toPure_296_);
v___f_298_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__2), 8, 4);
lean_closure_set(v___f_298_, 0, v_toBind_295_);
lean_closure_set(v___f_298_, 1, v___f_297_);
lean_closure_set(v___f_298_, 2, v_inst_291_);
lean_closure_set(v___f_298_, 3, v_lift_293_);
return v___f_298_;
}
}
LEAN_EXPORT lean_object* l_Std_IteratorLoop_finiteForIn_x27___boxed(lean_object* v_m_299_, lean_object* v_n_300_, lean_object* v_00_u03b1_301_, lean_object* v_00_u03b2_302_, lean_object* v_inst_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_lift_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Std_IteratorLoop_finiteForIn_x27(v_m_299_, v_n_300_, v_00_u03b1_301_, v_00_u03b2_302_, v_inst_303_, v_inst_304_, v_inst_305_, v_lift_306_);
lean_dec(v_inst_303_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg___lam__0(lean_object* v_inst_308_, lean_object* v_toBind_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_f_312_, lean_object* v_x_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_apply_2(v_inst_308_, lean_box(0), v_x_313_);
v___x_315_ = lean_apply_4(v_toBind_309_, lean_box(0), lean_box(0), v___x_314_, v_f_312_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg___lam__3(lean_object* v_toBind_316_, lean_object* v___f_317_, lean_object* v_inst_318_, lean_object* v___f_319_, lean_object* v_00_u03b3_320_, lean_object* v_it_321_, lean_object* v_init_322_, lean_object* v_f_323_){
_start:
{
lean_object* v___f_324_; lean_object* v___x_325_; 
v___f_324_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1), 6, 3);
lean_closure_set(v___f_324_, 0, v_f_323_);
lean_closure_set(v___f_324_, 1, v_toBind_316_);
lean_closure_set(v___f_324_, 2, v___f_317_);
v___x_325_ = lean_apply_6(v_inst_318_, v___f_319_, lean_box(0), lean_box(0), v_it_321_, v_init_322_, v___f_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___redArg(lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_inst_328_){
_start:
{
lean_object* v_toApplicative_329_; lean_object* v_toBind_330_; lean_object* v_toPure_331_; lean_object* v___f_332_; lean_object* v___f_333_; lean_object* v___f_334_; 
v_toApplicative_329_ = lean_ctor_get(v_inst_327_, 0);
lean_inc_ref(v_toApplicative_329_);
v_toBind_330_ = lean_ctor_get(v_inst_327_, 1);
lean_inc_n(v_toBind_330_, 2);
lean_dec_ref(v_inst_327_);
v_toPure_331_ = lean_ctor_get(v_toApplicative_329_, 1);
lean_inc(v_toPure_331_);
lean_dec_ref(v_toApplicative_329_);
v___f_332_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_332_, 0, v_inst_328_);
lean_closure_set(v___f_332_, 1, v_toBind_330_);
v___f_333_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_333_, 0, v_toPure_331_);
v___f_334_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_334_, 0, v_toBind_330_);
lean_closure_set(v___f_334_, 1, v___f_333_);
lean_closure_set(v___f_334_, 2, v_inst_326_);
lean_closure_set(v___f_334_, 3, v___f_332_);
return v___f_334_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27(lean_object* v_m_335_, lean_object* v_n_336_, lean_object* v_00_u03b1_337_, lean_object* v_00_u03b2_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_inst_341_, lean_object* v_inst_342_){
_start:
{
lean_object* v_toApplicative_343_; lean_object* v_toBind_344_; lean_object* v_toPure_345_; lean_object* v___f_346_; lean_object* v___f_347_; lean_object* v___f_348_; 
v_toApplicative_343_ = lean_ctor_get(v_inst_341_, 0);
lean_inc_ref(v_toApplicative_343_);
v_toBind_344_ = lean_ctor_get(v_inst_341_, 1);
lean_inc_n(v_toBind_344_, 2);
lean_dec_ref(v_inst_341_);
v_toPure_345_ = lean_ctor_get(v_toApplicative_343_, 1);
lean_inc(v_toPure_345_);
lean_dec_ref(v_toApplicative_343_);
v___f_346_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_346_, 0, v_inst_342_);
lean_closure_set(v___f_346_, 1, v_toBind_344_);
v___f_347_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_347_, 0, v_toPure_345_);
v___f_348_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_348_, 0, v_toBind_344_);
lean_closure_set(v___f_348_, 1, v___f_347_);
lean_closure_set(v___f_348_, 2, v_inst_340_);
lean_closure_set(v___f_348_, 3, v___f_346_);
return v___f_348_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForIn_x27___boxed(lean_object* v_m_349_, lean_object* v_n_350_, lean_object* v_00_u03b1_351_, lean_object* v_00_u03b2_352_, lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_inst_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Std_IterM_instForIn_x27(v_m_349_, v_n_350_, v_00_u03b1_351_, v_00_u03b2_352_, v_inst_353_, v_inst_354_, v_inst_355_, v_inst_356_);
lean_dec(v_inst_353_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop___redArg(lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_inst_360_){
_start:
{
lean_object* v_toApplicative_361_; lean_object* v_toBind_362_; lean_object* v_toPure_363_; lean_object* v___f_364_; lean_object* v___f_365_; lean_object* v___f_366_; lean_object* v___f_367_; 
v_toApplicative_361_ = lean_ctor_get(v_inst_360_, 0);
lean_inc_ref(v_toApplicative_361_);
v_toBind_362_ = lean_ctor_get(v_inst_360_, 1);
lean_inc_n(v_toBind_362_, 2);
lean_dec_ref(v_inst_360_);
v_toPure_363_ = lean_ctor_get(v_toApplicative_361_, 1);
lean_inc(v_toPure_363_);
lean_dec_ref(v_toApplicative_361_);
v___f_364_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_364_, 0, v_inst_359_);
lean_closure_set(v___f_364_, 1, v_toBind_362_);
v___f_365_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_365_, 0, v_toPure_363_);
v___f_366_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_366_, 0, v_toBind_362_);
lean_closure_set(v___f_366_, 1, v___f_365_);
lean_closure_set(v___f_366_, 2, v_inst_358_);
lean_closure_set(v___f_366_, 3, v___f_364_);
v___f_367_ = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(v___f_367_, 0, v___f_366_);
return v___f_367_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop(lean_object* v_m_368_, lean_object* v_n_369_, lean_object* v_00_u03b1_370_, lean_object* v_00_u03b2_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_inst_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Std_IterM_instForInOfIteratorLoop___redArg(v_inst_373_, v_inst_374_, v_inst_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForInOfIteratorLoop___boxed(lean_object* v_m_377_, lean_object* v_n_378_, lean_object* v_00_u03b1_379_, lean_object* v_00_u03b2_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_inst_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Std_IterM_instForInOfIteratorLoop(v_m_377_, v_n_378_, v_00_u03b1_379_, v_00_u03b2_380_, v_inst_381_, v_inst_382_, v_inst_383_, v_inst_384_);
lean_dec(v_inst_381_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___redArg___lam__3(lean_object* v_toBind_386_, lean_object* v___f_387_, lean_object* v_inst_388_, lean_object* v___f_389_, lean_object* v_00_u03b2_390_, lean_object* v_it_391_, lean_object* v_init_392_, lean_object* v_f_393_){
_start:
{
lean_object* v___f_394_; lean_object* v___x_395_; 
v___f_394_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__1), 6, 3);
lean_closure_set(v___f_394_, 0, v_f_393_);
lean_closure_set(v___f_394_, 1, v_toBind_386_);
lean_closure_set(v___f_394_, 2, v___f_387_);
v___x_395_ = lean_apply_6(v_inst_388_, v___f_389_, lean_box(0), lean_box(0), v_it_391_, v_init_392_, v___f_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___redArg(lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_inst_398_){
_start:
{
lean_object* v_toApplicative_399_; lean_object* v_toBind_400_; lean_object* v_toPure_401_; lean_object* v___f_402_; lean_object* v___f_403_; lean_object* v___f_404_; 
v_toApplicative_399_ = lean_ctor_get(v_inst_398_, 0);
lean_inc_ref(v_toApplicative_399_);
v_toBind_400_ = lean_ctor_get(v_inst_398_, 1);
lean_inc_n(v_toBind_400_, 2);
lean_dec_ref(v_inst_398_);
v_toPure_401_ = lean_ctor_get(v_toApplicative_399_, 1);
lean_inc(v_toPure_401_);
lean_dec_ref(v_toApplicative_399_);
v___f_402_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_402_, 0, v_inst_397_);
lean_closure_set(v___f_402_, 1, v_toBind_400_);
v___f_403_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_403_, 0, v_toPure_401_);
v___f_404_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_404_, 0, v_toBind_400_);
lean_closure_set(v___f_404_, 1, v___f_403_);
lean_closure_set(v___f_404_, 2, v_inst_396_);
lean_closure_set(v___f_404_, 3, v___f_402_);
return v___f_404_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27(lean_object* v_m_405_, lean_object* v_n_406_, lean_object* v_00_u03b1_407_, lean_object* v_00_u03b2_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_inst_412_){
_start:
{
lean_object* v_toApplicative_413_; lean_object* v_toBind_414_; lean_object* v_toPure_415_; lean_object* v___f_416_; lean_object* v___f_417_; lean_object* v___f_418_; 
v_toApplicative_413_ = lean_ctor_get(v_inst_412_, 0);
lean_inc_ref(v_toApplicative_413_);
v_toBind_414_ = lean_ctor_get(v_inst_412_, 1);
lean_inc_n(v_toBind_414_, 2);
lean_dec_ref(v_inst_412_);
v_toPure_415_ = lean_ctor_get(v_toApplicative_413_, 1);
lean_inc(v_toPure_415_);
lean_dec_ref(v_toApplicative_413_);
v___f_416_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_416_, 0, v_inst_411_);
lean_closure_set(v___f_416_, 1, v_toBind_414_);
v___f_417_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_417_, 0, v_toPure_415_);
v___f_418_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_418_, 0, v_toBind_414_);
lean_closure_set(v___f_418_, 1, v___f_417_);
lean_closure_set(v___f_418_, 2, v_inst_410_);
lean_closure_set(v___f_418_, 3, v___f_416_);
return v___f_418_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForIn_x27___boxed(lean_object* v_m_419_, lean_object* v_n_420_, lean_object* v_00_u03b1_421_, lean_object* v_00_u03b2_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_inst_425_, lean_object* v_inst_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Std_IterM_Partial_instForIn_x27(v_m_419_, v_n_420_, v_00_u03b1_421_, v_00_u03b2_422_, v_inst_423_, v_inst_424_, v_inst_425_, v_inst_426_);
lean_dec(v_inst_423_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27___redArg(lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_inst_430_){
_start:
{
lean_object* v_toApplicative_431_; lean_object* v_toBind_432_; lean_object* v_toPure_433_; lean_object* v___f_434_; lean_object* v___f_435_; lean_object* v___f_436_; 
v_toApplicative_431_ = lean_ctor_get(v_inst_430_, 0);
lean_inc_ref(v_toApplicative_431_);
v_toBind_432_ = lean_ctor_get(v_inst_430_, 1);
lean_inc_n(v_toBind_432_, 2);
lean_dec_ref(v_inst_430_);
v_toPure_433_ = lean_ctor_get(v_toApplicative_431_, 1);
lean_inc(v_toPure_433_);
lean_dec_ref(v_toApplicative_431_);
v___f_434_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_434_, 0, v_inst_429_);
lean_closure_set(v___f_434_, 1, v_toBind_432_);
v___f_435_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_435_, 0, v_toPure_433_);
v___f_436_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_436_, 0, v_toBind_432_);
lean_closure_set(v___f_436_, 1, v___f_435_);
lean_closure_set(v___f_436_, 2, v_inst_428_);
lean_closure_set(v___f_436_, 3, v___f_434_);
return v___f_436_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27(lean_object* v_m_437_, lean_object* v_n_438_, lean_object* v_00_u03b1_439_, lean_object* v_00_u03b2_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_inst_445_){
_start:
{
lean_object* v_toApplicative_446_; lean_object* v_toBind_447_; lean_object* v_toPure_448_; lean_object* v___f_449_; lean_object* v___f_450_; lean_object* v___f_451_; 
v_toApplicative_446_ = lean_ctor_get(v_inst_444_, 0);
lean_inc_ref(v_toApplicative_446_);
v_toBind_447_ = lean_ctor_get(v_inst_444_, 1);
lean_inc_n(v_toBind_447_, 2);
lean_dec_ref(v_inst_444_);
v_toPure_448_ = lean_ctor_get(v_toApplicative_446_, 1);
lean_inc(v_toPure_448_);
lean_dec_ref(v_toApplicative_446_);
v___f_449_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_449_, 0, v_inst_443_);
lean_closure_set(v___f_449_, 1, v_toBind_447_);
v___f_450_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_450_, 0, v_toPure_448_);
v___f_451_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_451_, 0, v_toBind_447_);
lean_closure_set(v___f_451_, 1, v___f_450_);
lean_closure_set(v___f_451_, 2, v_inst_442_);
lean_closure_set(v___f_451_, 3, v___f_449_);
return v___f_451_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_instForIn_x27___boxed(lean_object* v_m_452_, lean_object* v_n_453_, lean_object* v_00_u03b1_454_, lean_object* v_00_u03b2_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_inst_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Std_IterM_Total_instForIn_x27(v_m_452_, v_n_453_, v_00_u03b1_454_, v_00_u03b2_455_, v_inst_456_, v_inst_457_, v_inst_458_, v_inst_459_, v_inst_460_);
lean_dec(v_inst_456_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop___redArg(lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_inst_464_){
_start:
{
lean_object* v_toApplicative_465_; lean_object* v_toBind_466_; lean_object* v_toPure_467_; lean_object* v___f_468_; lean_object* v___f_469_; lean_object* v___f_470_; lean_object* v___f_471_; 
v_toApplicative_465_ = lean_ctor_get(v_inst_464_, 0);
lean_inc_ref(v_toApplicative_465_);
v_toBind_466_ = lean_ctor_get(v_inst_464_, 1);
lean_inc_n(v_toBind_466_, 2);
lean_dec_ref(v_inst_464_);
v_toPure_467_ = lean_ctor_get(v_toApplicative_465_, 1);
lean_inc(v_toPure_467_);
lean_dec_ref(v_toApplicative_465_);
v___f_468_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_468_, 0, v_inst_463_);
lean_closure_set(v___f_468_, 1, v_toBind_466_);
v___f_469_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_469_, 0, v_toPure_467_);
v___f_470_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_470_, 0, v_toBind_466_);
lean_closure_set(v___f_470_, 1, v___f_469_);
lean_closure_set(v___f_470_, 2, v_inst_462_);
lean_closure_set(v___f_470_, 3, v___f_468_);
v___f_471_ = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(v___f_471_, 0, v___f_470_);
return v___f_471_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop(lean_object* v_m_472_, lean_object* v_n_473_, lean_object* v_00_u03b1_474_, lean_object* v_00_u03b2_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_inst_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Std_IterM_Partial_instForInOfIteratorLoop___redArg(v_inst_477_, v_inst_478_, v_inst_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForInOfIteratorLoop___boxed(lean_object* v_m_481_, lean_object* v_n_482_, lean_object* v_00_u03b1_483_, lean_object* v_00_u03b2_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_inst_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Std_IterM_Partial_instForInOfIteratorLoop(v_m_481_, v_n_482_, v_00_u03b1_483_, v_00_u03b2_484_, v_inst_485_, v_inst_486_, v_inst_487_, v_inst_488_);
lean_dec(v_inst_485_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___redArg(lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_inst_492_){
_start:
{
lean_object* v_toApplicative_493_; lean_object* v_toBind_494_; lean_object* v_toPure_495_; lean_object* v___f_496_; lean_object* v___f_497_; lean_object* v___f_498_; lean_object* v___f_499_; 
v_toApplicative_493_ = lean_ctor_get(v_inst_492_, 0);
lean_inc_ref(v_toApplicative_493_);
v_toBind_494_ = lean_ctor_get(v_inst_492_, 1);
lean_inc_n(v_toBind_494_, 2);
lean_dec_ref(v_inst_492_);
v_toPure_495_ = lean_ctor_get(v_toApplicative_493_, 1);
lean_inc(v_toPure_495_);
lean_dec_ref(v_toApplicative_493_);
v___f_496_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_496_, 0, v_inst_491_);
lean_closure_set(v___f_496_, 1, v_toBind_494_);
v___f_497_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_497_, 0, v_toPure_495_);
v___f_498_ = lean_alloc_closure((void*)(l_Std_IterM_Partial_instForIn_x27___redArg___lam__3), 8, 4);
lean_closure_set(v___f_498_, 0, v_toBind_494_);
lean_closure_set(v___f_498_, 1, v___f_497_);
lean_closure_set(v___f_498_, 2, v_inst_490_);
lean_closure_set(v___f_498_, 3, v___f_496_);
v___f_499_ = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(v___f_499_, 0, v___f_498_);
return v___f_499_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite(lean_object* v_m_500_, lean_object* v_n_501_, lean_object* v_00_u03b1_502_, lean_object* v_00_u03b2_503_, lean_object* v_inst_504_, lean_object* v_inst_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_inst_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___redArg(v_inst_505_, v_inst_506_, v_inst_507_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite___boxed(lean_object* v_m_510_, lean_object* v_n_511_, lean_object* v_00_u03b1_512_, lean_object* v_00_u03b2_513_, lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_inst_517_, lean_object* v_inst_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_instForInTotalOfIteratorLoopOfMonadLiftTOfMonadOfFinite(v_m_510_, v_n_511_, v_00_u03b1_512_, v_00_u03b2_513_, v_inst_514_, v_inst_515_, v_inst_516_, v_inst_517_, v_inst_518_);
lean_dec(v_inst_514_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1(lean_object* v_toPure_520_, lean_object* v_____do__lift_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_apply_2(v_toPure_520_, lean_box(0), v_____do__lift_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__0(lean_object* v___x_523_, lean_object* v_toPure_524_, lean_object* v_____r_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_523_);
v___x_527_ = lean_apply_2(v_toPure_524_, lean_box(0), v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__2(lean_object* v_f_528_, lean_object* v_toBind_529_, lean_object* v___f_530_, lean_object* v___f_531_, lean_object* v_x1_532_, lean_object* v_x2_533_, lean_object* v_x3_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = lean_apply_1(v_f_528_, v_x1_532_);
lean_inc(v_toBind_529_);
v___x_536_ = lean_apply_4(v_toBind_529_, lean_box(0), lean_box(0), v___x_535_, v___f_530_);
v___x_537_ = lean_apply_4(v_toBind_529_, lean_box(0), lean_box(0), v___x_536_, v___f_531_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3(lean_object* v_toPure_538_, lean_object* v_toBind_539_, lean_object* v___f_540_, lean_object* v_inst_541_, lean_object* v___f_542_, lean_object* v_it_543_, lean_object* v_f_544_){
_start:
{
lean_object* v___x_545_; lean_object* v___f_546_; lean_object* v___f_547_; lean_object* v___x_548_; 
v___x_545_ = lean_box(0);
v___f_546_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__0), 3, 2);
lean_closure_set(v___f_546_, 0, v___x_545_);
lean_closure_set(v___f_546_, 1, v_toPure_538_);
v___f_547_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__2), 7, 4);
lean_closure_set(v___f_547_, 0, v_f_544_);
lean_closure_set(v___f_547_, 1, v_toBind_539_);
lean_closure_set(v___f_547_, 2, v___f_546_);
lean_closure_set(v___f_547_, 3, v___f_540_);
v___x_548_ = lean_apply_6(v_inst_541_, v___f_542_, lean_box(0), lean_box(0), v_it_543_, v___x_545_, v___f_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___redArg(lean_object* v_inst_549_, lean_object* v_inst_550_, lean_object* v_inst_551_){
_start:
{
lean_object* v_toApplicative_552_; lean_object* v_toBind_553_; lean_object* v_toPure_554_; lean_object* v___f_555_; lean_object* v___f_556_; lean_object* v___f_557_; 
v_toApplicative_552_ = lean_ctor_get(v_inst_550_, 0);
lean_inc_ref(v_toApplicative_552_);
v_toBind_553_ = lean_ctor_get(v_inst_550_, 1);
lean_inc_n(v_toBind_553_, 2);
lean_dec_ref(v_inst_550_);
v_toPure_554_ = lean_ctor_get(v_toApplicative_552_, 1);
lean_inc_n(v_toPure_554_, 2);
lean_dec_ref(v_toApplicative_552_);
v___f_555_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_555_, 0, v_inst_551_);
lean_closure_set(v___f_555_, 1, v_toBind_553_);
v___f_556_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_556_, 0, v_toPure_554_);
v___f_557_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3), 7, 5);
lean_closure_set(v___f_557_, 0, v_toPure_554_);
lean_closure_set(v___f_557_, 1, v_toBind_553_);
lean_closure_set(v___f_557_, 2, v___f_556_);
lean_closure_set(v___f_557_, 3, v_inst_549_);
lean_closure_set(v___f_557_, 4, v___f_555_);
return v___f_557_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop(lean_object* v_m_558_, lean_object* v_n_559_, lean_object* v_00_u03b1_560_, lean_object* v_00_u03b2_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_inst_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Std_IterM_instForMOfIteratorLoop___redArg(v_inst_563_, v_inst_564_, v_inst_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_instForMOfIteratorLoop___boxed(lean_object* v_m_567_, lean_object* v_n_568_, lean_object* v_00_u03b1_569_, lean_object* v_00_u03b2_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_inst_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_IterM_instForMOfIteratorLoop(v_m_567_, v_n_568_, v_00_u03b1_569_, v_00_u03b2_570_, v_inst_571_, v_inst_572_, v_inst_573_, v_inst_574_);
lean_dec(v_inst_571_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop___redArg(lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_){
_start:
{
lean_object* v_toApplicative_579_; lean_object* v_toBind_580_; lean_object* v_toPure_581_; lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___f_584_; 
v_toApplicative_579_ = lean_ctor_get(v_inst_576_, 0);
lean_inc_ref(v_toApplicative_579_);
v_toBind_580_ = lean_ctor_get(v_inst_576_, 1);
lean_inc_n(v_toBind_580_, 2);
lean_dec_ref(v_inst_576_);
v_toPure_581_ = lean_ctor_get(v_toApplicative_579_, 1);
lean_inc_n(v_toPure_581_, 2);
lean_dec_ref(v_toApplicative_579_);
v___f_582_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_582_, 0, v_inst_578_);
lean_closure_set(v___f_582_, 1, v_toBind_580_);
v___f_583_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_583_, 0, v_toPure_581_);
v___f_584_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3), 7, 5);
lean_closure_set(v___f_584_, 0, v_toPure_581_);
lean_closure_set(v___f_584_, 1, v_toBind_580_);
lean_closure_set(v___f_584_, 2, v___f_583_);
lean_closure_set(v___f_584_, 3, v_inst_577_);
lean_closure_set(v___f_584_, 4, v___f_582_);
return v___f_584_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop(lean_object* v_m_585_, lean_object* v_n_586_, lean_object* v_00_u03b1_587_, lean_object* v_00_u03b2_588_, lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Std_IterM_Partial_instForMOfItreratorLoop___redArg(v_inst_589_, v_inst_591_, v_inst_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_instForMOfItreratorLoop___boxed(lean_object* v_m_594_, lean_object* v_n_595_, lean_object* v_00_u03b1_596_, lean_object* v_00_u03b2_597_, lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_inst_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_IterM_Partial_instForMOfItreratorLoop(v_m_594_, v_n_595_, v_00_u03b1_596_, v_00_u03b2_597_, v_inst_598_, v_inst_599_, v_inst_600_, v_inst_601_);
lean_dec(v_inst_599_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___redArg(lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_inst_605_){
_start:
{
lean_object* v_toApplicative_606_; lean_object* v_toBind_607_; lean_object* v_toPure_608_; lean_object* v___f_609_; lean_object* v___f_610_; lean_object* v___f_611_; 
v_toApplicative_606_ = lean_ctor_get(v_inst_604_, 0);
lean_inc_ref(v_toApplicative_606_);
v_toBind_607_ = lean_ctor_get(v_inst_604_, 1);
lean_inc_n(v_toBind_607_, 2);
lean_dec_ref(v_inst_604_);
v_toPure_608_ = lean_ctor_get(v_toApplicative_606_, 1);
lean_inc_n(v_toPure_608_, 2);
lean_dec_ref(v_toApplicative_606_);
v___f_609_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_609_, 0, v_inst_605_);
lean_closure_set(v___f_609_, 1, v_toBind_607_);
v___f_610_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_610_, 0, v_toPure_608_);
v___f_611_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__3), 7, 5);
lean_closure_set(v___f_611_, 0, v_toPure_608_);
lean_closure_set(v___f_611_, 1, v_toBind_607_);
lean_closure_set(v___f_611_, 2, v___f_610_);
lean_closure_set(v___f_611_, 3, v_inst_603_);
lean_closure_set(v___f_611_, 4, v___f_609_);
return v___f_611_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite(lean_object* v_m_612_, lean_object* v_n_613_, lean_object* v_00_u03b1_614_, lean_object* v_00_u03b2_615_, lean_object* v_inst_616_, lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_inst_619_, lean_object* v_inst_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___redArg(v_inst_617_, v_inst_618_, v_inst_619_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite___boxed(lean_object* v_m_622_, lean_object* v_n_623_, lean_object* v_00_u03b1_624_, lean_object* v_00_u03b2_625_, lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_inst_629_, lean_object* v_inst_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Std_instForMTotalOfIteratorLoopOfMonadOfMonadLiftTOfFinite(v_m_622_, v_n_623_, v_00_u03b1_624_, v_00_u03b2_625_, v_inst_626_, v_inst_627_, v_inst_628_, v_inst_629_, v_inst_630_);
lean_dec(v_inst_626_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg___lam__0(lean_object* v_a_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v_a_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg___lam__3(lean_object* v_toFunctor_634_, lean_object* v_f_635_, lean_object* v___f_636_, lean_object* v_toBind_637_, lean_object* v___f_638_, lean_object* v_x1_639_, lean_object* v_x2_640_, lean_object* v_x3_641_){
_start:
{
lean_object* v_map_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v_map_642_ = lean_ctor_get(v_toFunctor_634_, 0);
lean_inc(v_map_642_);
lean_dec_ref(v_toFunctor_634_);
v___x_643_ = lean_apply_2(v_f_635_, v_x3_641_, v_x1_639_);
v___x_644_ = lean_apply_4(v_map_642_, lean_box(0), lean_box(0), v___f_636_, v___x_643_);
v___x_645_ = lean_apply_4(v_toBind_637_, lean_box(0), lean_box(0), v___x_644_, v___f_638_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___redArg(lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_f_650_, lean_object* v_init_651_, lean_object* v_it_652_){
_start:
{
lean_object* v_toApplicative_653_; lean_object* v_toBind_654_; lean_object* v_toFunctor_655_; lean_object* v_toPure_656_; lean_object* v___f_657_; lean_object* v___f_658_; lean_object* v___f_659_; lean_object* v___f_660_; lean_object* v___x_661_; 
v_toApplicative_653_ = lean_ctor_get(v_inst_647_, 0);
lean_inc_ref(v_toApplicative_653_);
v_toBind_654_ = lean_ctor_get(v_inst_647_, 1);
lean_inc_n(v_toBind_654_, 2);
lean_dec_ref(v_inst_647_);
v_toFunctor_655_ = lean_ctor_get(v_toApplicative_653_, 0);
lean_inc_ref(v_toFunctor_655_);
v_toPure_656_ = lean_ctor_get(v_toApplicative_653_, 1);
lean_inc(v_toPure_656_);
lean_dec_ref(v_toApplicative_653_);
v___f_657_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
v___f_658_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_658_, 0, v_inst_649_);
lean_closure_set(v___f_658_, 1, v_toBind_654_);
v___f_659_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_659_, 0, v_toPure_656_);
v___f_660_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_660_, 0, v_toFunctor_655_);
lean_closure_set(v___f_660_, 1, v_f_650_);
lean_closure_set(v___f_660_, 2, v___f_657_);
lean_closure_set(v___f_660_, 3, v_toBind_654_);
lean_closure_set(v___f_660_, 4, v___f_659_);
v___x_661_ = lean_apply_6(v_inst_648_, v___f_658_, lean_box(0), lean_box(0), v_it_652_, v_init_651_, v___f_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM(lean_object* v_m_662_, lean_object* v_n_663_, lean_object* v_inst_664_, lean_object* v_00_u03b1_665_, lean_object* v_00_u03b2_666_, lean_object* v_00_u03b3_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_inst_670_, lean_object* v_f_671_, lean_object* v_init_672_, lean_object* v_it_673_){
_start:
{
lean_object* v_toApplicative_674_; lean_object* v_toBind_675_; lean_object* v_toFunctor_676_; lean_object* v_toPure_677_; lean_object* v___f_678_; lean_object* v___f_679_; lean_object* v___f_680_; lean_object* v___f_681_; lean_object* v___x_682_; 
v_toApplicative_674_ = lean_ctor_get(v_inst_664_, 0);
lean_inc_ref(v_toApplicative_674_);
v_toBind_675_ = lean_ctor_get(v_inst_664_, 1);
lean_inc_n(v_toBind_675_, 2);
lean_dec_ref(v_inst_664_);
v_toFunctor_676_ = lean_ctor_get(v_toApplicative_674_, 0);
lean_inc_ref(v_toFunctor_676_);
v_toPure_677_ = lean_ctor_get(v_toApplicative_674_, 1);
lean_inc(v_toPure_677_);
lean_dec_ref(v_toApplicative_674_);
v___f_678_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
v___f_679_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_679_, 0, v_inst_670_);
lean_closure_set(v___f_679_, 1, v_toBind_675_);
v___f_680_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_680_, 0, v_toPure_677_);
v___f_681_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_681_, 0, v_toFunctor_676_);
lean_closure_set(v___f_681_, 1, v_f_671_);
lean_closure_set(v___f_681_, 2, v___f_678_);
lean_closure_set(v___f_681_, 3, v_toBind_675_);
lean_closure_set(v___f_681_, 4, v___f_680_);
v___x_682_ = lean_apply_6(v_inst_669_, v___f_679_, lean_box(0), lean_box(0), v_it_673_, v_init_672_, v___f_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_foldM___boxed(lean_object* v_m_683_, lean_object* v_n_684_, lean_object* v_inst_685_, lean_object* v_00_u03b1_686_, lean_object* v_00_u03b2_687_, lean_object* v_00_u03b3_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_f_692_, lean_object* v_init_693_, lean_object* v_it_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Std_IterM_foldM(v_m_683_, v_n_684_, v_inst_685_, v_00_u03b1_686_, v_00_u03b2_687_, v_00_u03b3_688_, v_inst_689_, v_inst_690_, v_inst_691_, v_f_692_, v_init_693_, v_it_694_);
lean_dec(v_inst_689_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM___redArg(lean_object* v_inst_696_, lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_f_699_, lean_object* v_init_700_, lean_object* v_it_701_){
_start:
{
lean_object* v_toApplicative_702_; lean_object* v_toBind_703_; lean_object* v_toFunctor_704_; lean_object* v_toPure_705_; lean_object* v___f_706_; lean_object* v___f_707_; lean_object* v___f_708_; lean_object* v___f_709_; lean_object* v___x_710_; 
v_toApplicative_702_ = lean_ctor_get(v_inst_696_, 0);
lean_inc_ref(v_toApplicative_702_);
v_toBind_703_ = lean_ctor_get(v_inst_696_, 1);
lean_inc_n(v_toBind_703_, 2);
lean_dec_ref(v_inst_696_);
v_toFunctor_704_ = lean_ctor_get(v_toApplicative_702_, 0);
lean_inc_ref(v_toFunctor_704_);
v_toPure_705_ = lean_ctor_get(v_toApplicative_702_, 1);
lean_inc(v_toPure_705_);
lean_dec_ref(v_toApplicative_702_);
v___f_706_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
v___f_707_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_707_, 0, v_inst_698_);
lean_closure_set(v___f_707_, 1, v_toBind_703_);
v___f_708_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_708_, 0, v_toPure_705_);
v___f_709_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_709_, 0, v_toFunctor_704_);
lean_closure_set(v___f_709_, 1, v_f_699_);
lean_closure_set(v___f_709_, 2, v___f_706_);
lean_closure_set(v___f_709_, 3, v_toBind_703_);
lean_closure_set(v___f_709_, 4, v___f_708_);
v___x_710_ = lean_apply_6(v_inst_697_, v___f_707_, lean_box(0), lean_box(0), v_it_701_, v_init_700_, v___f_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM(lean_object* v_m_711_, lean_object* v_n_712_, lean_object* v_inst_713_, lean_object* v_00_u03b1_714_, lean_object* v_00_u03b2_715_, lean_object* v_00_u03b3_716_, lean_object* v_inst_717_, lean_object* v_inst_718_, lean_object* v_inst_719_, lean_object* v_f_720_, lean_object* v_init_721_, lean_object* v_it_722_){
_start:
{
lean_object* v_toApplicative_723_; lean_object* v_toBind_724_; lean_object* v_toFunctor_725_; lean_object* v_toPure_726_; lean_object* v___f_727_; lean_object* v___f_728_; lean_object* v___f_729_; lean_object* v___f_730_; lean_object* v___x_731_; 
v_toApplicative_723_ = lean_ctor_get(v_inst_713_, 0);
lean_inc_ref(v_toApplicative_723_);
v_toBind_724_ = lean_ctor_get(v_inst_713_, 1);
lean_inc_n(v_toBind_724_, 2);
lean_dec_ref(v_inst_713_);
v_toFunctor_725_ = lean_ctor_get(v_toApplicative_723_, 0);
lean_inc_ref(v_toFunctor_725_);
v_toPure_726_ = lean_ctor_get(v_toApplicative_723_, 1);
lean_inc(v_toPure_726_);
lean_dec_ref(v_toApplicative_723_);
v___f_727_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
v___f_728_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_728_, 0, v_inst_719_);
lean_closure_set(v___f_728_, 1, v_toBind_724_);
v___f_729_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_729_, 0, v_toPure_726_);
v___f_730_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_730_, 0, v_toFunctor_725_);
lean_closure_set(v___f_730_, 1, v_f_720_);
lean_closure_set(v___f_730_, 2, v___f_727_);
lean_closure_set(v___f_730_, 3, v_toBind_724_);
lean_closure_set(v___f_730_, 4, v___f_729_);
v___x_731_ = lean_apply_6(v_inst_718_, v___f_728_, lean_box(0), lean_box(0), v_it_722_, v_init_721_, v___f_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_foldM___boxed(lean_object* v_m_732_, lean_object* v_n_733_, lean_object* v_inst_734_, lean_object* v_00_u03b1_735_, lean_object* v_00_u03b2_736_, lean_object* v_00_u03b3_737_, lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_f_741_, lean_object* v_init_742_, lean_object* v_it_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Std_IterM_Partial_foldM(v_m_732_, v_n_733_, v_inst_734_, v_00_u03b1_735_, v_00_u03b2_736_, v_00_u03b3_737_, v_inst_738_, v_inst_739_, v_inst_740_, v_f_741_, v_init_742_, v_it_743_);
lean_dec(v_inst_738_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM___redArg(lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_f_748_, lean_object* v_init_749_, lean_object* v_it_750_){
_start:
{
lean_object* v_toApplicative_751_; lean_object* v_toBind_752_; lean_object* v_toFunctor_753_; lean_object* v_toPure_754_; lean_object* v___f_755_; lean_object* v___f_756_; lean_object* v___f_757_; lean_object* v___f_758_; lean_object* v___x_759_; 
v_toApplicative_751_ = lean_ctor_get(v_inst_745_, 0);
lean_inc_ref(v_toApplicative_751_);
v_toBind_752_ = lean_ctor_get(v_inst_745_, 1);
lean_inc_n(v_toBind_752_, 2);
lean_dec_ref(v_inst_745_);
v_toFunctor_753_ = lean_ctor_get(v_toApplicative_751_, 0);
lean_inc_ref(v_toFunctor_753_);
v_toPure_754_ = lean_ctor_get(v_toApplicative_751_, 1);
lean_inc(v_toPure_754_);
lean_dec_ref(v_toApplicative_751_);
v___f_755_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
v___f_756_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_756_, 0, v_inst_747_);
lean_closure_set(v___f_756_, 1, v_toBind_752_);
v___f_757_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_757_, 0, v_toPure_754_);
v___f_758_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_758_, 0, v_toFunctor_753_);
lean_closure_set(v___f_758_, 1, v_f_748_);
lean_closure_set(v___f_758_, 2, v___f_755_);
lean_closure_set(v___f_758_, 3, v_toBind_752_);
lean_closure_set(v___f_758_, 4, v___f_757_);
v___x_759_ = lean_apply_6(v_inst_746_, v___f_756_, lean_box(0), lean_box(0), v_it_750_, v_init_749_, v___f_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM(lean_object* v_m_760_, lean_object* v_n_761_, lean_object* v_inst_762_, lean_object* v_00_u03b1_763_, lean_object* v_00_u03b2_764_, lean_object* v_00_u03b3_765_, lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_inst_768_, lean_object* v_inst_769_, lean_object* v_f_770_, lean_object* v_init_771_, lean_object* v_it_772_){
_start:
{
lean_object* v_toApplicative_773_; lean_object* v_toBind_774_; lean_object* v_toFunctor_775_; lean_object* v_toPure_776_; lean_object* v___f_777_; lean_object* v___f_778_; lean_object* v___f_779_; lean_object* v___f_780_; lean_object* v___x_781_; 
v_toApplicative_773_ = lean_ctor_get(v_inst_762_, 0);
lean_inc_ref(v_toApplicative_773_);
v_toBind_774_ = lean_ctor_get(v_inst_762_, 1);
lean_inc_n(v_toBind_774_, 2);
lean_dec_ref(v_inst_762_);
v_toFunctor_775_ = lean_ctor_get(v_toApplicative_773_, 0);
lean_inc_ref(v_toFunctor_775_);
v_toPure_776_ = lean_ctor_get(v_toApplicative_773_, 1);
lean_inc(v_toPure_776_);
lean_dec_ref(v_toApplicative_773_);
v___f_777_ = ((lean_object*)(l_Std_IterM_foldM___redArg___closed__0));
v___f_778_ = lean_alloc_closure((void*)(l_Std_IterM_instForIn_x27___redArg___lam__0), 6, 2);
lean_closure_set(v___f_778_, 0, v_inst_768_);
lean_closure_set(v___f_778_, 1, v_toBind_774_);
v___f_779_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_779_, 0, v_toPure_776_);
v___f_780_ = lean_alloc_closure((void*)(l_Std_IterM_foldM___redArg___lam__3), 8, 5);
lean_closure_set(v___f_780_, 0, v_toFunctor_775_);
lean_closure_set(v___f_780_, 1, v_f_770_);
lean_closure_set(v___f_780_, 2, v___f_777_);
lean_closure_set(v___f_780_, 3, v_toBind_774_);
lean_closure_set(v___f_780_, 4, v___f_779_);
v___x_781_ = lean_apply_6(v_inst_767_, v___f_778_, lean_box(0), lean_box(0), v_it_772_, v_init_771_, v___f_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_foldM___boxed(lean_object* v_m_782_, lean_object* v_n_783_, lean_object* v_inst_784_, lean_object* v_00_u03b1_785_, lean_object* v_00_u03b2_786_, lean_object* v_00_u03b3_787_, lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_f_792_, lean_object* v_init_793_, lean_object* v_it_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Std_IterM_Total_foldM(v_m_782_, v_n_783_, v_inst_784_, v_00_u03b1_785_, v_00_u03b2_786_, v_00_u03b3_787_, v_inst_788_, v_inst_789_, v_inst_790_, v_inst_791_, v_f_792_, v_init_793_, v_it_794_);
lean_dec(v_inst_788_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg___lam__0(lean_object* v_toBind_796_, lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_f_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = lean_apply_4(v_toBind_796_, lean_box(0), lean_box(0), v_x_800_, v_f_799_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg___lam__2(lean_object* v_f_802_, lean_object* v_toPure_803_, lean_object* v_toBind_804_, lean_object* v___f_805_, lean_object* v_x1_806_, lean_object* v_x2_807_, lean_object* v_x3_808_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_809_ = lean_apply_2(v_f_802_, v_x3_808_, v_x1_806_);
v___x_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
v___x_811_ = lean_apply_2(v_toPure_803_, lean_box(0), v___x_810_);
v___x_812_ = lean_apply_4(v_toBind_804_, lean_box(0), lean_box(0), v___x_811_, v___f_805_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___redArg(lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_f_815_, lean_object* v_init_816_, lean_object* v_it_817_){
_start:
{
lean_object* v_toApplicative_818_; lean_object* v_toBind_819_; lean_object* v_toPure_820_; lean_object* v___f_821_; lean_object* v___f_822_; lean_object* v___f_823_; lean_object* v___x_824_; 
v_toApplicative_818_ = lean_ctor_get(v_inst_813_, 0);
lean_inc_ref(v_toApplicative_818_);
v_toBind_819_ = lean_ctor_get(v_inst_813_, 1);
lean_inc_n(v_toBind_819_, 2);
lean_dec_ref(v_inst_813_);
v_toPure_820_ = lean_ctor_get(v_toApplicative_818_, 1);
lean_inc_n(v_toPure_820_, 2);
lean_dec_ref(v_toApplicative_818_);
v___f_821_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_821_, 0, v_toBind_819_);
v___f_822_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_822_, 0, v_toPure_820_);
v___f_823_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_823_, 0, v_f_815_);
lean_closure_set(v___f_823_, 1, v_toPure_820_);
lean_closure_set(v___f_823_, 2, v_toBind_819_);
lean_closure_set(v___f_823_, 3, v___f_822_);
v___x_824_ = lean_apply_6(v_inst_814_, v___f_821_, lean_box(0), lean_box(0), v_it_817_, v_init_816_, v___f_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold(lean_object* v_m_825_, lean_object* v_00_u03b1_826_, lean_object* v_00_u03b2_827_, lean_object* v_00_u03b3_828_, lean_object* v_inst_829_, lean_object* v_inst_830_, lean_object* v_inst_831_, lean_object* v_f_832_, lean_object* v_init_833_, lean_object* v_it_834_){
_start:
{
lean_object* v_toApplicative_835_; lean_object* v_toBind_836_; lean_object* v_toPure_837_; lean_object* v___f_838_; lean_object* v___f_839_; lean_object* v___f_840_; lean_object* v___x_841_; 
v_toApplicative_835_ = lean_ctor_get(v_inst_829_, 0);
lean_inc_ref(v_toApplicative_835_);
v_toBind_836_ = lean_ctor_get(v_inst_829_, 1);
lean_inc_n(v_toBind_836_, 2);
lean_dec_ref(v_inst_829_);
v_toPure_837_ = lean_ctor_get(v_toApplicative_835_, 1);
lean_inc_n(v_toPure_837_, 2);
lean_dec_ref(v_toApplicative_835_);
v___f_838_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_838_, 0, v_toBind_836_);
v___f_839_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_839_, 0, v_toPure_837_);
v___f_840_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_840_, 0, v_f_832_);
lean_closure_set(v___f_840_, 1, v_toPure_837_);
lean_closure_set(v___f_840_, 2, v_toBind_836_);
lean_closure_set(v___f_840_, 3, v___f_839_);
v___x_841_ = lean_apply_6(v_inst_831_, v___f_838_, lean_box(0), lean_box(0), v_it_834_, v_init_833_, v___f_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_fold___boxed(lean_object* v_m_842_, lean_object* v_00_u03b1_843_, lean_object* v_00_u03b2_844_, lean_object* v_00_u03b3_845_, lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_f_849_, lean_object* v_init_850_, lean_object* v_it_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_IterM_fold(v_m_842_, v_00_u03b1_843_, v_00_u03b2_844_, v_00_u03b3_845_, v_inst_846_, v_inst_847_, v_inst_848_, v_f_849_, v_init_850_, v_it_851_);
lean_dec(v_inst_847_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold___redArg(lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_f_855_, lean_object* v_init_856_, lean_object* v_it_857_){
_start:
{
lean_object* v_toApplicative_858_; lean_object* v_toBind_859_; lean_object* v_toPure_860_; lean_object* v___f_861_; lean_object* v___f_862_; lean_object* v___f_863_; lean_object* v___x_864_; 
v_toApplicative_858_ = lean_ctor_get(v_inst_853_, 0);
lean_inc_ref(v_toApplicative_858_);
v_toBind_859_ = lean_ctor_get(v_inst_853_, 1);
lean_inc_n(v_toBind_859_, 2);
lean_dec_ref(v_inst_853_);
v_toPure_860_ = lean_ctor_get(v_toApplicative_858_, 1);
lean_inc_n(v_toPure_860_, 2);
lean_dec_ref(v_toApplicative_858_);
v___f_861_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_861_, 0, v_toBind_859_);
v___f_862_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_862_, 0, v_toPure_860_);
v___f_863_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_863_, 0, v_f_855_);
lean_closure_set(v___f_863_, 1, v_toPure_860_);
lean_closure_set(v___f_863_, 2, v_toBind_859_);
lean_closure_set(v___f_863_, 3, v___f_862_);
v___x_864_ = lean_apply_6(v_inst_854_, v___f_861_, lean_box(0), lean_box(0), v_it_857_, v_init_856_, v___f_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold(lean_object* v_m_865_, lean_object* v_00_u03b1_866_, lean_object* v_00_u03b2_867_, lean_object* v_00_u03b3_868_, lean_object* v_inst_869_, lean_object* v_inst_870_, lean_object* v_inst_871_, lean_object* v_f_872_, lean_object* v_init_873_, lean_object* v_it_874_){
_start:
{
lean_object* v_toApplicative_875_; lean_object* v_toBind_876_; lean_object* v_toPure_877_; lean_object* v___f_878_; lean_object* v___f_879_; lean_object* v___f_880_; lean_object* v___x_881_; 
v_toApplicative_875_ = lean_ctor_get(v_inst_869_, 0);
lean_inc_ref(v_toApplicative_875_);
v_toBind_876_ = lean_ctor_get(v_inst_869_, 1);
lean_inc_n(v_toBind_876_, 2);
lean_dec_ref(v_inst_869_);
v_toPure_877_ = lean_ctor_get(v_toApplicative_875_, 1);
lean_inc_n(v_toPure_877_, 2);
lean_dec_ref(v_toApplicative_875_);
v___f_878_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_878_, 0, v_toBind_876_);
v___f_879_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_879_, 0, v_toPure_877_);
v___f_880_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_880_, 0, v_f_872_);
lean_closure_set(v___f_880_, 1, v_toPure_877_);
lean_closure_set(v___f_880_, 2, v_toBind_876_);
lean_closure_set(v___f_880_, 3, v___f_879_);
v___x_881_ = lean_apply_6(v_inst_871_, v___f_878_, lean_box(0), lean_box(0), v_it_874_, v_init_873_, v___f_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_fold___boxed(lean_object* v_m_882_, lean_object* v_00_u03b1_883_, lean_object* v_00_u03b2_884_, lean_object* v_00_u03b3_885_, lean_object* v_inst_886_, lean_object* v_inst_887_, lean_object* v_inst_888_, lean_object* v_f_889_, lean_object* v_init_890_, lean_object* v_it_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_IterM_Partial_fold(v_m_882_, v_00_u03b1_883_, v_00_u03b2_884_, v_00_u03b3_885_, v_inst_886_, v_inst_887_, v_inst_888_, v_f_889_, v_init_890_, v_it_891_);
lean_dec(v_inst_887_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold___redArg(lean_object* v_inst_893_, lean_object* v_inst_894_, lean_object* v_f_895_, lean_object* v_init_896_, lean_object* v_it_897_){
_start:
{
lean_object* v_toApplicative_898_; lean_object* v_toBind_899_; lean_object* v_toPure_900_; lean_object* v___f_901_; lean_object* v___f_902_; lean_object* v___f_903_; lean_object* v___x_904_; 
v_toApplicative_898_ = lean_ctor_get(v_inst_893_, 0);
lean_inc_ref(v_toApplicative_898_);
v_toBind_899_ = lean_ctor_get(v_inst_893_, 1);
lean_inc_n(v_toBind_899_, 2);
lean_dec_ref(v_inst_893_);
v_toPure_900_ = lean_ctor_get(v_toApplicative_898_, 1);
lean_inc_n(v_toPure_900_, 2);
lean_dec_ref(v_toApplicative_898_);
v___f_901_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_901_, 0, v_toBind_899_);
v___f_902_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_902_, 0, v_toPure_900_);
v___f_903_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_903_, 0, v_f_895_);
lean_closure_set(v___f_903_, 1, v_toPure_900_);
lean_closure_set(v___f_903_, 2, v_toBind_899_);
lean_closure_set(v___f_903_, 3, v___f_902_);
v___x_904_ = lean_apply_6(v_inst_894_, v___f_901_, lean_box(0), lean_box(0), v_it_897_, v_init_896_, v___f_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold(lean_object* v_m_905_, lean_object* v_00_u03b1_906_, lean_object* v_00_u03b2_907_, lean_object* v_00_u03b3_908_, lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_inst_911_, lean_object* v_inst_912_, lean_object* v_f_913_, lean_object* v_init_914_, lean_object* v_it_915_){
_start:
{
lean_object* v_toApplicative_916_; lean_object* v_toBind_917_; lean_object* v_toPure_918_; lean_object* v___f_919_; lean_object* v___f_920_; lean_object* v___f_921_; lean_object* v___x_922_; 
v_toApplicative_916_ = lean_ctor_get(v_inst_909_, 0);
lean_inc_ref(v_toApplicative_916_);
v_toBind_917_ = lean_ctor_get(v_inst_909_, 1);
lean_inc_n(v_toBind_917_, 2);
lean_dec_ref(v_inst_909_);
v_toPure_918_ = lean_ctor_get(v_toApplicative_916_, 1);
lean_inc_n(v_toPure_918_, 2);
lean_dec_ref(v_toApplicative_916_);
v___f_919_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_919_, 0, v_toBind_917_);
v___f_920_ = lean_alloc_closure((void*)(l_Std_IteratorLoop_finiteForIn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_920_, 0, v_toPure_918_);
v___f_921_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__2), 7, 4);
lean_closure_set(v___f_921_, 0, v_f_913_);
lean_closure_set(v___f_921_, 1, v_toPure_918_);
lean_closure_set(v___f_921_, 2, v_toBind_917_);
lean_closure_set(v___f_921_, 3, v___f_920_);
v___x_922_ = lean_apply_6(v_inst_911_, v___f_919_, lean_box(0), lean_box(0), v_it_915_, v_init_914_, v___f_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_fold___boxed(lean_object* v_m_923_, lean_object* v_00_u03b1_924_, lean_object* v_00_u03b2_925_, lean_object* v_00_u03b3_926_, lean_object* v_inst_927_, lean_object* v_inst_928_, lean_object* v_inst_929_, lean_object* v_inst_930_, lean_object* v_f_931_, lean_object* v_init_932_, lean_object* v_it_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Std_IterM_Total_fold(v_m_923_, v_00_u03b1_924_, v_00_u03b2_925_, v_00_u03b3_926_, v_inst_927_, v_inst_928_, v_inst_929_, v_inst_930_, v_f_931_, v_init_932_, v_it_933_);
lean_dec(v_inst_928_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg___lam__2(lean_object* v___x_935_, lean_object* v_toPure_936_, lean_object* v_toBind_937_, lean_object* v___f_938_, lean_object* v_x1_939_, lean_object* v_x2_940_, lean_object* v_x3_941_){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_935_);
v___x_943_ = lean_apply_2(v_toPure_936_, lean_box(0), v___x_942_);
v___x_944_ = lean_apply_4(v_toBind_937_, lean_box(0), lean_box(0), v___x_943_, v___f_938_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg___lam__2___boxed(lean_object* v___x_945_, lean_object* v_toPure_946_, lean_object* v_toBind_947_, lean_object* v___f_948_, lean_object* v_x1_949_, lean_object* v_x2_950_, lean_object* v_x3_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Std_IterM_drain___redArg___lam__2(v___x_945_, v_toPure_946_, v_toBind_947_, v___f_948_, v_x1_949_, v_x2_950_, v_x3_951_);
lean_dec(v_x1_949_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___redArg(lean_object* v_inst_953_, lean_object* v_it_954_, lean_object* v_inst_955_){
_start:
{
lean_object* v_toApplicative_956_; lean_object* v_toBind_957_; lean_object* v_toPure_958_; lean_object* v___x_959_; lean_object* v___f_960_; lean_object* v___f_961_; lean_object* v___f_962_; lean_object* v___x_963_; 
v_toApplicative_956_ = lean_ctor_get(v_inst_953_, 0);
lean_inc_ref(v_toApplicative_956_);
v_toBind_957_ = lean_ctor_get(v_inst_953_, 1);
lean_inc_n(v_toBind_957_, 2);
lean_dec_ref(v_inst_953_);
v_toPure_958_ = lean_ctor_get(v_toApplicative_956_, 1);
lean_inc_n(v_toPure_958_, 2);
lean_dec_ref(v_toApplicative_956_);
v___x_959_ = lean_box(0);
v___f_960_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_960_, 0, v_toBind_957_);
v___f_961_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_961_, 0, v_toPure_958_);
v___f_962_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_962_, 0, v___x_959_);
lean_closure_set(v___f_962_, 1, v_toPure_958_);
lean_closure_set(v___f_962_, 2, v_toBind_957_);
lean_closure_set(v___f_962_, 3, v___f_961_);
v___x_963_ = lean_apply_6(v_inst_955_, v___f_960_, lean_box(0), lean_box(0), v_it_954_, v___x_959_, v___f_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain(lean_object* v_00_u03b1_964_, lean_object* v_m_965_, lean_object* v_inst_966_, lean_object* v_00_u03b2_967_, lean_object* v_inst_968_, lean_object* v_it_969_, lean_object* v_inst_970_){
_start:
{
lean_object* v_toApplicative_971_; lean_object* v_toBind_972_; lean_object* v_toPure_973_; lean_object* v___x_974_; lean_object* v___f_975_; lean_object* v___f_976_; lean_object* v___f_977_; lean_object* v___x_978_; 
v_toApplicative_971_ = lean_ctor_get(v_inst_966_, 0);
lean_inc_ref(v_toApplicative_971_);
v_toBind_972_ = lean_ctor_get(v_inst_966_, 1);
lean_inc_n(v_toBind_972_, 2);
lean_dec_ref(v_inst_966_);
v_toPure_973_ = lean_ctor_get(v_toApplicative_971_, 1);
lean_inc_n(v_toPure_973_, 2);
lean_dec_ref(v_toApplicative_971_);
v___x_974_ = lean_box(0);
v___f_975_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_975_, 0, v_toBind_972_);
v___f_976_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_976_, 0, v_toPure_973_);
v___f_977_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_977_, 0, v___x_974_);
lean_closure_set(v___f_977_, 1, v_toPure_973_);
lean_closure_set(v___f_977_, 2, v_toBind_972_);
lean_closure_set(v___f_977_, 3, v___f_976_);
v___x_978_ = lean_apply_6(v_inst_970_, v___f_975_, lean_box(0), lean_box(0), v_it_969_, v___x_974_, v___f_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drain___boxed(lean_object* v_00_u03b1_979_, lean_object* v_m_980_, lean_object* v_inst_981_, lean_object* v_00_u03b2_982_, lean_object* v_inst_983_, lean_object* v_it_984_, lean_object* v_inst_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Std_IterM_drain(v_00_u03b1_979_, v_m_980_, v_inst_981_, v_00_u03b2_982_, v_inst_983_, v_it_984_, v_inst_985_);
lean_dec(v_inst_983_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain___redArg(lean_object* v_inst_987_, lean_object* v_it_988_, lean_object* v_inst_989_){
_start:
{
lean_object* v_toApplicative_990_; lean_object* v_toBind_991_; lean_object* v_toPure_992_; lean_object* v___x_993_; lean_object* v___f_994_; lean_object* v___f_995_; lean_object* v___f_996_; lean_object* v___x_997_; 
v_toApplicative_990_ = lean_ctor_get(v_inst_987_, 0);
lean_inc_ref(v_toApplicative_990_);
v_toBind_991_ = lean_ctor_get(v_inst_987_, 1);
lean_inc_n(v_toBind_991_, 2);
lean_dec_ref(v_inst_987_);
v_toPure_992_ = lean_ctor_get(v_toApplicative_990_, 1);
lean_inc_n(v_toPure_992_, 2);
lean_dec_ref(v_toApplicative_990_);
v___x_993_ = lean_box(0);
v___f_994_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_994_, 0, v_toBind_991_);
v___f_995_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_995_, 0, v_toPure_992_);
v___f_996_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_996_, 0, v___x_993_);
lean_closure_set(v___f_996_, 1, v_toPure_992_);
lean_closure_set(v___f_996_, 2, v_toBind_991_);
lean_closure_set(v___f_996_, 3, v___f_995_);
v___x_997_ = lean_apply_6(v_inst_989_, v___f_994_, lean_box(0), lean_box(0), v_it_988_, v___x_993_, v___f_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain(lean_object* v_00_u03b1_998_, lean_object* v_m_999_, lean_object* v_inst_1000_, lean_object* v_00_u03b2_1001_, lean_object* v_inst_1002_, lean_object* v_it_1003_, lean_object* v_inst_1004_){
_start:
{
lean_object* v_toApplicative_1005_; lean_object* v_toBind_1006_; lean_object* v_toPure_1007_; lean_object* v___x_1008_; lean_object* v___f_1009_; lean_object* v___f_1010_; lean_object* v___f_1011_; lean_object* v___x_1012_; 
v_toApplicative_1005_ = lean_ctor_get(v_inst_1000_, 0);
lean_inc_ref(v_toApplicative_1005_);
v_toBind_1006_ = lean_ctor_get(v_inst_1000_, 1);
lean_inc_n(v_toBind_1006_, 2);
lean_dec_ref(v_inst_1000_);
v_toPure_1007_ = lean_ctor_get(v_toApplicative_1005_, 1);
lean_inc_n(v_toPure_1007_, 2);
lean_dec_ref(v_toApplicative_1005_);
v___x_1008_ = lean_box(0);
v___f_1009_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1009_, 0, v_toBind_1006_);
v___f_1010_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1010_, 0, v_toPure_1007_);
v___f_1011_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1011_, 0, v___x_1008_);
lean_closure_set(v___f_1011_, 1, v_toPure_1007_);
lean_closure_set(v___f_1011_, 2, v_toBind_1006_);
lean_closure_set(v___f_1011_, 3, v___f_1010_);
v___x_1012_ = lean_apply_6(v_inst_1004_, v___f_1009_, lean_box(0), lean_box(0), v_it_1003_, v___x_1008_, v___f_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_drain___boxed(lean_object* v_00_u03b1_1013_, lean_object* v_m_1014_, lean_object* v_inst_1015_, lean_object* v_00_u03b2_1016_, lean_object* v_inst_1017_, lean_object* v_it_1018_, lean_object* v_inst_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Std_IterM_Partial_drain(v_00_u03b1_1013_, v_m_1014_, v_inst_1015_, v_00_u03b2_1016_, v_inst_1017_, v_it_1018_, v_inst_1019_);
lean_dec(v_inst_1017_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain___redArg(lean_object* v_inst_1021_, lean_object* v_it_1022_, lean_object* v_inst_1023_){
_start:
{
lean_object* v_toApplicative_1024_; lean_object* v_toBind_1025_; lean_object* v_toPure_1026_; lean_object* v___x_1027_; lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v___f_1030_; lean_object* v___x_1031_; 
v_toApplicative_1024_ = lean_ctor_get(v_inst_1021_, 0);
lean_inc_ref(v_toApplicative_1024_);
v_toBind_1025_ = lean_ctor_get(v_inst_1021_, 1);
lean_inc_n(v_toBind_1025_, 2);
lean_dec_ref(v_inst_1021_);
v_toPure_1026_ = lean_ctor_get(v_toApplicative_1024_, 1);
lean_inc_n(v_toPure_1026_, 2);
lean_dec_ref(v_toApplicative_1024_);
v___x_1027_ = lean_box(0);
v___f_1028_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1028_, 0, v_toBind_1025_);
v___f_1029_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1029_, 0, v_toPure_1026_);
v___f_1030_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1030_, 0, v___x_1027_);
lean_closure_set(v___f_1030_, 1, v_toPure_1026_);
lean_closure_set(v___f_1030_, 2, v_toBind_1025_);
lean_closure_set(v___f_1030_, 3, v___f_1029_);
v___x_1031_ = lean_apply_6(v_inst_1023_, v___f_1028_, lean_box(0), lean_box(0), v_it_1022_, v___x_1027_, v___f_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain(lean_object* v_00_u03b1_1032_, lean_object* v_m_1033_, lean_object* v_inst_1034_, lean_object* v_00_u03b2_1035_, lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_it_1038_, lean_object* v_inst_1039_){
_start:
{
lean_object* v_toApplicative_1040_; lean_object* v_toBind_1041_; lean_object* v_toPure_1042_; lean_object* v___x_1043_; lean_object* v___f_1044_; lean_object* v___f_1045_; lean_object* v___f_1046_; lean_object* v___x_1047_; 
v_toApplicative_1040_ = lean_ctor_get(v_inst_1034_, 0);
lean_inc_ref(v_toApplicative_1040_);
v_toBind_1041_ = lean_ctor_get(v_inst_1034_, 1);
lean_inc_n(v_toBind_1041_, 2);
lean_dec_ref(v_inst_1034_);
v_toPure_1042_ = lean_ctor_get(v_toApplicative_1040_, 1);
lean_inc_n(v_toPure_1042_, 2);
lean_dec_ref(v_toApplicative_1040_);
v___x_1043_ = lean_box(0);
v___f_1044_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1044_, 0, v_toBind_1041_);
v___f_1045_ = lean_alloc_closure((void*)(l_Std_IterM_instForMOfIteratorLoop___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1045_, 0, v_toPure_1042_);
v___f_1046_ = lean_alloc_closure((void*)(l_Std_IterM_drain___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1046_, 0, v___x_1043_);
lean_closure_set(v___f_1046_, 1, v_toPure_1042_);
lean_closure_set(v___f_1046_, 2, v_toBind_1041_);
lean_closure_set(v___f_1046_, 3, v___f_1045_);
v___x_1047_ = lean_apply_6(v_inst_1039_, v___f_1044_, lean_box(0), lean_box(0), v_it_1038_, v___x_1043_, v___f_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_drain___boxed(lean_object* v_00_u03b1_1048_, lean_object* v_m_1049_, lean_object* v_inst_1050_, lean_object* v_00_u03b2_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_it_1054_, lean_object* v_inst_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Std_IterM_Total_drain(v_00_u03b1_1048_, v_m_1049_, v_inst_1050_, v_00_u03b2_1051_, v_inst_1052_, v_inst_1053_, v_it_1054_, v_inst_1055_);
lean_dec(v_inst_1052_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__1(lean_object* v_toPure_1057_, lean_object* v_____do__lift_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_apply_2(v_toPure_1057_, lean_box(0), v_____do__lift_1058_);
return v___x_1059_;
}
}
lean_object* l_Std_IterM_anyM___redArg___lam__0(uint8_t v___x_1060_, lean_object* v_toPure_1061_, uint8_t v_____do__lift_1062_){
_start:
{
if (v_____do__lift_1062_ == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = lean_box(v___x_1060_);
v___x_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
v___x_1065_ = lean_apply_2(v_toPure_1061_, lean_box(0), v___x_1064_);
return v___x_1065_;
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1066_ = lean_box(v_____do__lift_1062_);
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
v___x_1068_ = lean_apply_2(v_toPure_1061_, lean_box(0), v___x_1067_);
return v___x_1068_;
}
}
}
LEAN_EXPORT void l_Std_IterM_anyM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1060_ = stack[0].m_num;
lean_object* v_toPure_1061_ = stack[1].m_obj;
uint8_t v_____do__lift_1062_ = stack[2].m_num;
lean_object* v_res_1069_;
v_res_1069_ = l_Std_IterM_anyM___redArg___lam__0(v___x_1060_, v_toPure_1061_, v_____do__lift_1062_);
stack->m_obj
 = v_res_1069_;
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__0___boxed(lean_object* v___x_1070_, lean_object* v_toPure_1071_, lean_object* v_____do__lift_1072_){
_start:
{
uint8_t v___x_157__boxed_1073_; uint8_t v_____do__lift_158__boxed_1074_; lean_object* v_res_1075_; 
v___x_157__boxed_1073_ = lean_unbox(v___x_1070_);
v_____do__lift_158__boxed_1074_ = lean_unbox(v_____do__lift_1072_);
v_res_1075_ = l_Std_IterM_anyM___redArg___lam__0(v___x_157__boxed_1073_, v_toPure_1071_, v_____do__lift_158__boxed_1074_);
return v_res_1075_;
}
}
lean_object* l_Std_IterM_anyM___redArg___lam__2(lean_object* v_p_1076_, lean_object* v_toBind_1077_, lean_object* v___f_1078_, lean_object* v___f_1079_, lean_object* v_x1_1080_, lean_object* v_x2_1081_, uint8_t v_x3_1082_){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1083_ = lean_apply_1(v_p_1076_, v_x1_1080_);
lean_inc(v_toBind_1077_);
v___x_1084_ = lean_apply_4(v_toBind_1077_, lean_box(0), lean_box(0), v___x_1083_, v___f_1078_);
v___x_1085_ = lean_apply_4(v_toBind_1077_, lean_box(0), lean_box(0), v___x_1084_, v___f_1079_);
return v___x_1085_;
}
}
LEAN_EXPORT void l_Std_IterM_anyM___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1076_ = stack[0].m_obj;
lean_object* v_toBind_1077_ = stack[1].m_obj;
lean_object* v___f_1078_ = stack[2].m_obj;
lean_object* v___f_1079_ = stack[3].m_obj;
lean_object* v_x1_1080_ = stack[4].m_obj;
uint8_t v_x3_1082_ = stack[6].m_num;
lean_object* v_res_1086_;
v_res_1086_ = l_Std_IterM_anyM___redArg___lam__2(v_p_1076_, v_toBind_1077_, v___f_1078_, v___f_1079_, v_x1_1080_, lean_box(0), v_x3_1082_);
stack->m_obj
 = v_res_1086_;
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg___lam__2___boxed(lean_object* v_p_1087_, lean_object* v_toBind_1088_, lean_object* v___f_1089_, lean_object* v___f_1090_, lean_object* v_x1_1091_, lean_object* v_x2_1092_, lean_object* v_x3_1093_){
_start:
{
uint8_t v_x3_189__boxed_1094_; lean_object* v_res_1095_; 
v_x3_189__boxed_1094_ = lean_unbox(v_x3_1093_);
v_res_1095_ = l_Std_IterM_anyM___redArg___lam__2(v_p_1087_, v_toBind_1088_, v___f_1089_, v___f_1090_, v_x1_1091_, v_x2_1092_, v_x3_189__boxed_1094_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___redArg(lean_object* v_inst_1096_, lean_object* v_inst_1097_, lean_object* v_p_1098_, lean_object* v_it_1099_){
_start:
{
lean_object* v_toApplicative_1100_; lean_object* v_toBind_1101_; lean_object* v_toPure_1102_; lean_object* v___f_1103_; lean_object* v___f_1104_; uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___f_1107_; lean_object* v___f_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_toApplicative_1100_ = lean_ctor_get(v_inst_1096_, 0);
lean_inc_ref(v_toApplicative_1100_);
v_toBind_1101_ = lean_ctor_get(v_inst_1096_, 1);
lean_inc_n(v_toBind_1101_, 2);
lean_dec_ref(v_inst_1096_);
v_toPure_1102_ = lean_ctor_get(v_toApplicative_1100_, 1);
lean_inc_n(v_toPure_1102_, 2);
lean_dec_ref(v_toApplicative_1100_);
v___f_1103_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1103_, 0, v_toBind_1101_);
v___f_1104_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1104_, 0, v_toPure_1102_);
v___x_1105_ = 0;
v___x_1106_ = lean_box(v___x_1105_);
v___f_1107_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1107_, 0, v___x_1106_);
lean_closure_set(v___f_1107_, 1, v_toPure_1102_);
v___f_1108_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1108_, 0, v_p_1098_);
lean_closure_set(v___f_1108_, 1, v_toBind_1101_);
lean_closure_set(v___f_1108_, 2, v___f_1107_);
lean_closure_set(v___f_1108_, 3, v___f_1104_);
v___x_1109_ = lean_box(v___x_1105_);
v___x_1110_ = lean_apply_6(v_inst_1097_, v___f_1103_, lean_box(0), lean_box(0), v_it_1099_, v___x_1109_, v___f_1108_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM(lean_object* v_00_u03b1_1111_, lean_object* v_00_u03b2_1112_, lean_object* v_m_1113_, lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_inst_1116_, lean_object* v_p_1117_, lean_object* v_it_1118_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Std_IterM_anyM___redArg(v_inst_1114_, v_inst_1116_, v_p_1117_, v_it_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_anyM___boxed(lean_object* v_00_u03b1_1120_, lean_object* v_00_u03b2_1121_, lean_object* v_m_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_p_1126_, lean_object* v_it_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Std_IterM_anyM(v_00_u03b1_1120_, v_00_u03b2_1121_, v_m_1122_, v_inst_1123_, v_inst_1124_, v_inst_1125_, v_p_1126_, v_it_1127_);
lean_dec(v_inst_1124_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM___redArg(lean_object* v_inst_1129_, lean_object* v_inst_1130_, lean_object* v_p_1131_, lean_object* v_it_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Std_IterM_anyM___redArg(v_inst_1129_, v_inst_1130_, v_p_1131_, v_it_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM(lean_object* v_00_u03b1_1134_, lean_object* v_00_u03b2_1135_, lean_object* v_m_1136_, lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_p_1140_, lean_object* v_it_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Std_IterM_anyM___redArg(v_inst_1137_, v_inst_1139_, v_p_1140_, v_it_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_anyM___boxed(lean_object* v_00_u03b1_1143_, lean_object* v_00_u03b2_1144_, lean_object* v_m_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_inst_1148_, lean_object* v_p_1149_, lean_object* v_it_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Std_IterM_Partial_anyM(v_00_u03b1_1143_, v_00_u03b2_1144_, v_m_1145_, v_inst_1146_, v_inst_1147_, v_inst_1148_, v_p_1149_, v_it_1150_);
lean_dec(v_inst_1147_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM___redArg(lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_p_1154_, lean_object* v_it_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Std_IterM_anyM___redArg(v_inst_1152_, v_inst_1153_, v_p_1154_, v_it_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM(lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_m_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_inst_1162_, lean_object* v_inst_1163_, lean_object* v_p_1164_, lean_object* v_it_1165_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Std_IterM_anyM___redArg(v_inst_1160_, v_inst_1162_, v_p_1164_, v_it_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_anyM___boxed(lean_object* v_00_u03b1_1167_, lean_object* v_00_u03b2_1168_, lean_object* v_m_1169_, lean_object* v_inst_1170_, lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_inst_1173_, lean_object* v_p_1174_, lean_object* v_it_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Std_IterM_Total_anyM(v_00_u03b1_1167_, v_00_u03b2_1168_, v_m_1169_, v_inst_1170_, v_inst_1171_, v_inst_1172_, v_inst_1173_, v_p_1174_, v_it_1175_);
lean_dec(v_inst_1171_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any___redArg___lam__0(lean_object* v_p_1177_, lean_object* v_toPure_1178_, lean_object* v_x_1179_){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_apply_1(v_p_1177_, v_x_1179_);
v___x_1181_ = lean_apply_2(v_toPure_1178_, lean_box(0), v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any___redArg(lean_object* v_inst_1182_, lean_object* v_inst_1183_, lean_object* v_p_1184_, lean_object* v_it_1185_){
_start:
{
lean_object* v_toApplicative_1186_; lean_object* v_toPure_1187_; lean_object* v___f_1188_; lean_object* v___x_1189_; 
v_toApplicative_1186_ = lean_ctor_get(v_inst_1182_, 0);
v_toPure_1187_ = lean_ctor_get(v_toApplicative_1186_, 1);
lean_inc(v_toPure_1187_);
v___f_1188_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1188_, 0, v_p_1184_);
lean_closure_set(v___f_1188_, 1, v_toPure_1187_);
v___x_1189_ = l_Std_IterM_anyM___redArg(v_inst_1182_, v_inst_1183_, v___f_1188_, v_it_1185_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any(lean_object* v_00_u03b1_1190_, lean_object* v_00_u03b2_1191_, lean_object* v_m_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_p_1196_, lean_object* v_it_1197_){
_start:
{
lean_object* v_toApplicative_1198_; lean_object* v_toPure_1199_; lean_object* v___f_1200_; lean_object* v___x_1201_; 
v_toApplicative_1198_ = lean_ctor_get(v_inst_1193_, 0);
v_toPure_1199_ = lean_ctor_get(v_toApplicative_1198_, 1);
lean_inc(v_toPure_1199_);
v___f_1200_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1200_, 0, v_p_1196_);
lean_closure_set(v___f_1200_, 1, v_toPure_1199_);
v___x_1201_ = l_Std_IterM_anyM___redArg(v_inst_1193_, v_inst_1195_, v___f_1200_, v_it_1197_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_any___boxed(lean_object* v_00_u03b1_1202_, lean_object* v_00_u03b2_1203_, lean_object* v_m_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_inst_1207_, lean_object* v_p_1208_, lean_object* v_it_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Std_IterM_any(v_00_u03b1_1202_, v_00_u03b2_1203_, v_m_1204_, v_inst_1205_, v_inst_1206_, v_inst_1207_, v_p_1208_, v_it_1209_);
lean_dec(v_inst_1206_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any___redArg(lean_object* v_inst_1211_, lean_object* v_inst_1212_, lean_object* v_p_1213_, lean_object* v_it_1214_){
_start:
{
lean_object* v_toApplicative_1215_; lean_object* v_toPure_1216_; lean_object* v___f_1217_; lean_object* v___x_1218_; 
v_toApplicative_1215_ = lean_ctor_get(v_inst_1211_, 0);
v_toPure_1216_ = lean_ctor_get(v_toApplicative_1215_, 1);
lean_inc(v_toPure_1216_);
v___f_1217_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1217_, 0, v_p_1213_);
lean_closure_set(v___f_1217_, 1, v_toPure_1216_);
v___x_1218_ = l_Std_IterM_anyM___redArg(v_inst_1211_, v_inst_1212_, v___f_1217_, v_it_1214_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any(lean_object* v_00_u03b1_1219_, lean_object* v_00_u03b2_1220_, lean_object* v_m_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_p_1225_, lean_object* v_it_1226_){
_start:
{
lean_object* v_toApplicative_1227_; lean_object* v_toPure_1228_; lean_object* v___f_1229_; lean_object* v___x_1230_; 
v_toApplicative_1227_ = lean_ctor_get(v_inst_1222_, 0);
v_toPure_1228_ = lean_ctor_get(v_toApplicative_1227_, 1);
lean_inc(v_toPure_1228_);
v___f_1229_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1229_, 0, v_p_1225_);
lean_closure_set(v___f_1229_, 1, v_toPure_1228_);
v___x_1230_ = l_Std_IterM_anyM___redArg(v_inst_1222_, v_inst_1224_, v___f_1229_, v_it_1226_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_any___boxed(lean_object* v_00_u03b1_1231_, lean_object* v_00_u03b2_1232_, lean_object* v_m_1233_, lean_object* v_inst_1234_, lean_object* v_inst_1235_, lean_object* v_inst_1236_, lean_object* v_p_1237_, lean_object* v_it_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Std_IterM_Partial_any(v_00_u03b1_1231_, v_00_u03b2_1232_, v_m_1233_, v_inst_1234_, v_inst_1235_, v_inst_1236_, v_p_1237_, v_it_1238_);
lean_dec(v_inst_1235_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_any___redArg(lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_p_1242_, lean_object* v_it_1243_){
_start:
{
lean_object* v_toApplicative_1244_; lean_object* v_toPure_1245_; lean_object* v___f_1246_; lean_object* v___x_1247_; 
v_toApplicative_1244_ = lean_ctor_get(v_inst_1240_, 0);
v_toPure_1245_ = lean_ctor_get(v_toApplicative_1244_, 1);
lean_inc(v_toPure_1245_);
v___f_1246_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1246_, 0, v_p_1242_);
lean_closure_set(v___f_1246_, 1, v_toPure_1245_);
v___x_1247_ = l_Std_IterM_anyM___redArg(v_inst_1240_, v_inst_1241_, v___f_1246_, v_it_1243_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_any(lean_object* v_00_u03b1_1248_, lean_object* v_00_u03b2_1249_, lean_object* v_m_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_inst_1254_, lean_object* v_p_1255_, lean_object* v_it_1256_){
_start:
{
lean_object* v_toApplicative_1257_; lean_object* v_toPure_1258_; lean_object* v___f_1259_; lean_object* v___x_1260_; 
v_toApplicative_1257_ = lean_ctor_get(v_inst_1251_, 0);
v_toPure_1258_ = lean_ctor_get(v_toApplicative_1257_, 1);
lean_inc(v_toPure_1258_);
v___f_1259_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1259_, 0, v_p_1255_);
lean_closure_set(v___f_1259_, 1, v_toPure_1258_);
v___x_1260_ = l_Std_IterM_anyM___redArg(v_inst_1251_, v_inst_1253_, v___f_1259_, v_it_1256_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_any___boxed(lean_object* v_00_u03b1_1261_, lean_object* v_00_u03b2_1262_, lean_object* v_m_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_inst_1267_, lean_object* v_p_1268_, lean_object* v_it_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Std_IterM_Total_any(v_00_u03b1_1261_, v_00_u03b2_1262_, v_m_1263_, v_inst_1264_, v_inst_1265_, v_inst_1266_, v_inst_1267_, v_p_1268_, v_it_1269_);
lean_dec(v_inst_1265_);
return v_res_1270_;
}
}
lean_object* l_Std_IterM_allM___redArg___lam__2(lean_object* v_toPure_1271_, uint8_t v___x_1272_, uint8_t v_____do__lift_1273_){
_start:
{
if (v_____do__lift_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = lean_box(v_____do__lift_1273_);
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
v___x_1276_ = lean_apply_2(v_toPure_1271_, lean_box(0), v___x_1275_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = lean_box(v___x_1272_);
v___x_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
v___x_1279_ = lean_apply_2(v_toPure_1271_, lean_box(0), v___x_1278_);
return v___x_1279_;
}
}
}
LEAN_EXPORT void l_Std_IterM_allM___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_1271_ = stack[0].m_obj;
uint8_t v___x_1272_ = stack[1].m_num;
uint8_t v_____do__lift_1273_ = stack[2].m_num;
lean_object* v_res_1280_;
v_res_1280_ = l_Std_IterM_allM___redArg___lam__2(v_toPure_1271_, v___x_1272_, v_____do__lift_1273_);
stack->m_obj
 = v_res_1280_;
}
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg___lam__2___boxed(lean_object* v_toPure_1281_, lean_object* v___x_1282_, lean_object* v_____do__lift_1283_){
_start:
{
uint8_t v___x_149__boxed_1284_; uint8_t v_____do__lift_150__boxed_1285_; lean_object* v_res_1286_; 
v___x_149__boxed_1284_ = lean_unbox(v___x_1282_);
v_____do__lift_150__boxed_1285_ = lean_unbox(v_____do__lift_1283_);
v_res_1286_ = l_Std_IterM_allM___redArg___lam__2(v_toPure_1281_, v___x_149__boxed_1284_, v_____do__lift_150__boxed_1285_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM___redArg(lean_object* v_inst_1287_, lean_object* v_inst_1288_, lean_object* v_p_1289_, lean_object* v_it_1290_){
_start:
{
lean_object* v_toApplicative_1291_; lean_object* v_toBind_1292_; lean_object* v_toPure_1293_; lean_object* v___f_1294_; lean_object* v___f_1295_; uint8_t v___x_1296_; lean_object* v___x_1297_; lean_object* v___f_1298_; lean_object* v___f_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v_toApplicative_1291_ = lean_ctor_get(v_inst_1287_, 0);
lean_inc_ref(v_toApplicative_1291_);
v_toBind_1292_ = lean_ctor_get(v_inst_1287_, 1);
lean_inc_n(v_toBind_1292_, 2);
lean_dec_ref(v_inst_1287_);
v_toPure_1293_ = lean_ctor_get(v_toApplicative_1291_, 1);
lean_inc_n(v_toPure_1293_, 2);
lean_dec_ref(v_toApplicative_1291_);
v___f_1294_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1294_, 0, v_toBind_1292_);
v___f_1295_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1295_, 0, v_toPure_1293_);
v___x_1296_ = 1;
v___x_1297_ = lean_box(v___x_1296_);
v___f_1298_ = lean_alloc_closure((void*)(l_Std_IterM_allM___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1298_, 0, v_toPure_1293_);
lean_closure_set(v___f_1298_, 1, v___x_1297_);
v___f_1299_ = lean_alloc_closure((void*)(l_Std_IterM_anyM___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1299_, 0, v_p_1289_);
lean_closure_set(v___f_1299_, 1, v_toBind_1292_);
lean_closure_set(v___f_1299_, 2, v___f_1298_);
lean_closure_set(v___f_1299_, 3, v___f_1295_);
v___x_1300_ = lean_box(v___x_1296_);
v___x_1301_ = lean_apply_6(v_inst_1288_, v___f_1294_, lean_box(0), lean_box(0), v_it_1290_, v___x_1300_, v___f_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM(lean_object* v_00_u03b1_1302_, lean_object* v_00_u03b2_1303_, lean_object* v_m_1304_, lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_p_1308_, lean_object* v_it_1309_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Std_IterM_allM___redArg(v_inst_1305_, v_inst_1307_, v_p_1308_, v_it_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_allM___boxed(lean_object* v_00_u03b1_1311_, lean_object* v_00_u03b2_1312_, lean_object* v_m_1313_, lean_object* v_inst_1314_, lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_p_1317_, lean_object* v_it_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Std_IterM_allM(v_00_u03b1_1311_, v_00_u03b2_1312_, v_m_1313_, v_inst_1314_, v_inst_1315_, v_inst_1316_, v_p_1317_, v_it_1318_);
lean_dec(v_inst_1315_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM___redArg(lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v_p_1322_, lean_object* v_it_1323_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Std_IterM_allM___redArg(v_inst_1320_, v_inst_1321_, v_p_1322_, v_it_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM(lean_object* v_00_u03b1_1325_, lean_object* v_00_u03b2_1326_, lean_object* v_m_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_p_1331_, lean_object* v_it_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Std_IterM_allM___redArg(v_inst_1328_, v_inst_1330_, v_p_1331_, v_it_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_allM___boxed(lean_object* v_00_u03b1_1334_, lean_object* v_00_u03b2_1335_, lean_object* v_m_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_inst_1339_, lean_object* v_p_1340_, lean_object* v_it_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Std_IterM_Partial_allM(v_00_u03b1_1334_, v_00_u03b2_1335_, v_m_1336_, v_inst_1337_, v_inst_1338_, v_inst_1339_, v_p_1340_, v_it_1341_);
lean_dec(v_inst_1338_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM___redArg(lean_object* v_inst_1343_, lean_object* v_inst_1344_, lean_object* v_p_1345_, lean_object* v_it_1346_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Std_IterM_allM___redArg(v_inst_1343_, v_inst_1344_, v_p_1345_, v_it_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM(lean_object* v_00_u03b1_1348_, lean_object* v_00_u03b2_1349_, lean_object* v_m_1350_, lean_object* v_inst_1351_, lean_object* v_inst_1352_, lean_object* v_inst_1353_, lean_object* v_inst_1354_, lean_object* v_p_1355_, lean_object* v_it_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Std_IterM_allM___redArg(v_inst_1351_, v_inst_1353_, v_p_1355_, v_it_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_allM___boxed(lean_object* v_00_u03b1_1358_, lean_object* v_00_u03b2_1359_, lean_object* v_m_1360_, lean_object* v_inst_1361_, lean_object* v_inst_1362_, lean_object* v_inst_1363_, lean_object* v_inst_1364_, lean_object* v_p_1365_, lean_object* v_it_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Std_IterM_Total_allM(v_00_u03b1_1358_, v_00_u03b2_1359_, v_m_1360_, v_inst_1361_, v_inst_1362_, v_inst_1363_, v_inst_1364_, v_p_1365_, v_it_1366_);
lean_dec(v_inst_1362_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_all___redArg(lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v_p_1370_, lean_object* v_it_1371_){
_start:
{
lean_object* v_toApplicative_1372_; lean_object* v_toPure_1373_; lean_object* v___f_1374_; lean_object* v___x_1375_; 
v_toApplicative_1372_ = lean_ctor_get(v_inst_1368_, 0);
v_toPure_1373_ = lean_ctor_get(v_toApplicative_1372_, 1);
lean_inc(v_toPure_1373_);
v___f_1374_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1374_, 0, v_p_1370_);
lean_closure_set(v___f_1374_, 1, v_toPure_1373_);
v___x_1375_ = l_Std_IterM_allM___redArg(v_inst_1368_, v_inst_1369_, v___f_1374_, v_it_1371_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_all(lean_object* v_00_u03b1_1376_, lean_object* v_00_u03b2_1377_, lean_object* v_m_1378_, lean_object* v_inst_1379_, lean_object* v_inst_1380_, lean_object* v_inst_1381_, lean_object* v_p_1382_, lean_object* v_it_1383_){
_start:
{
lean_object* v_toApplicative_1384_; lean_object* v_toPure_1385_; lean_object* v___f_1386_; lean_object* v___x_1387_; 
v_toApplicative_1384_ = lean_ctor_get(v_inst_1379_, 0);
v_toPure_1385_ = lean_ctor_get(v_toApplicative_1384_, 1);
lean_inc(v_toPure_1385_);
v___f_1386_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1386_, 0, v_p_1382_);
lean_closure_set(v___f_1386_, 1, v_toPure_1385_);
v___x_1387_ = l_Std_IterM_allM___redArg(v_inst_1379_, v_inst_1381_, v___f_1386_, v_it_1383_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_all___boxed(lean_object* v_00_u03b1_1388_, lean_object* v_00_u03b2_1389_, lean_object* v_m_1390_, lean_object* v_inst_1391_, lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_p_1394_, lean_object* v_it_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Std_IterM_all(v_00_u03b1_1388_, v_00_u03b2_1389_, v_m_1390_, v_inst_1391_, v_inst_1392_, v_inst_1393_, v_p_1394_, v_it_1395_);
lean_dec(v_inst_1392_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all___redArg(lean_object* v_inst_1397_, lean_object* v_inst_1398_, lean_object* v_p_1399_, lean_object* v_it_1400_){
_start:
{
lean_object* v_toApplicative_1401_; lean_object* v_toPure_1402_; lean_object* v___f_1403_; lean_object* v___x_1404_; 
v_toApplicative_1401_ = lean_ctor_get(v_inst_1397_, 0);
v_toPure_1402_ = lean_ctor_get(v_toApplicative_1401_, 1);
lean_inc(v_toPure_1402_);
v___f_1403_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1403_, 0, v_p_1399_);
lean_closure_set(v___f_1403_, 1, v_toPure_1402_);
v___x_1404_ = l_Std_IterM_allM___redArg(v_inst_1397_, v_inst_1398_, v___f_1403_, v_it_1400_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all(lean_object* v_00_u03b1_1405_, lean_object* v_00_u03b2_1406_, lean_object* v_m_1407_, lean_object* v_inst_1408_, lean_object* v_inst_1409_, lean_object* v_inst_1410_, lean_object* v_p_1411_, lean_object* v_it_1412_){
_start:
{
lean_object* v_toApplicative_1413_; lean_object* v_toPure_1414_; lean_object* v___f_1415_; lean_object* v___x_1416_; 
v_toApplicative_1413_ = lean_ctor_get(v_inst_1408_, 0);
v_toPure_1414_ = lean_ctor_get(v_toApplicative_1413_, 1);
lean_inc(v_toPure_1414_);
v___f_1415_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1415_, 0, v_p_1411_);
lean_closure_set(v___f_1415_, 1, v_toPure_1414_);
v___x_1416_ = l_Std_IterM_allM___redArg(v_inst_1408_, v_inst_1410_, v___f_1415_, v_it_1412_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_all___boxed(lean_object* v_00_u03b1_1417_, lean_object* v_00_u03b2_1418_, lean_object* v_m_1419_, lean_object* v_inst_1420_, lean_object* v_inst_1421_, lean_object* v_inst_1422_, lean_object* v_p_1423_, lean_object* v_it_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Std_IterM_Partial_all(v_00_u03b1_1417_, v_00_u03b2_1418_, v_m_1419_, v_inst_1420_, v_inst_1421_, v_inst_1422_, v_p_1423_, v_it_1424_);
lean_dec(v_inst_1421_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_all___redArg(lean_object* v_inst_1426_, lean_object* v_inst_1427_, lean_object* v_p_1428_, lean_object* v_it_1429_){
_start:
{
lean_object* v_toApplicative_1430_; lean_object* v_toPure_1431_; lean_object* v___f_1432_; lean_object* v___x_1433_; 
v_toApplicative_1430_ = lean_ctor_get(v_inst_1426_, 0);
v_toPure_1431_ = lean_ctor_get(v_toApplicative_1430_, 1);
lean_inc(v_toPure_1431_);
v___f_1432_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1432_, 0, v_p_1428_);
lean_closure_set(v___f_1432_, 1, v_toPure_1431_);
v___x_1433_ = l_Std_IterM_allM___redArg(v_inst_1426_, v_inst_1427_, v___f_1432_, v_it_1429_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_all(lean_object* v_00_u03b1_1434_, lean_object* v_00_u03b2_1435_, lean_object* v_m_1436_, lean_object* v_inst_1437_, lean_object* v_inst_1438_, lean_object* v_inst_1439_, lean_object* v_inst_1440_, lean_object* v_p_1441_, lean_object* v_it_1442_){
_start:
{
lean_object* v_toApplicative_1443_; lean_object* v_toPure_1444_; lean_object* v___f_1445_; lean_object* v___x_1446_; 
v_toApplicative_1443_ = lean_ctor_get(v_inst_1437_, 0);
v_toPure_1444_ = lean_ctor_get(v_toApplicative_1443_, 1);
lean_inc(v_toPure_1444_);
v___f_1445_ = lean_alloc_closure((void*)(l_Std_IterM_any___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1445_, 0, v_p_1441_);
lean_closure_set(v___f_1445_, 1, v_toPure_1444_);
v___x_1446_ = l_Std_IterM_allM___redArg(v_inst_1437_, v_inst_1439_, v___f_1445_, v_it_1442_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_all___boxed(lean_object* v_00_u03b1_1447_, lean_object* v_00_u03b2_1448_, lean_object* v_m_1449_, lean_object* v_inst_1450_, lean_object* v_inst_1451_, lean_object* v_inst_1452_, lean_object* v_inst_1453_, lean_object* v_p_1454_, lean_object* v_it_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Std_IterM_Total_all(v_00_u03b1_1447_, v_00_u03b2_1448_, v_m_1449_, v_inst_1450_, v_inst_1451_, v_inst_1452_, v_inst_1453_, v_p_1454_, v_it_1455_);
lean_dec(v_inst_1451_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__1(lean_object* v_toPure_1457_, lean_object* v_____do__lift_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_apply_2(v_toPure_1457_, lean_box(0), v_____do__lift_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__0(lean_object* v___x_1460_, lean_object* v_toPure_1461_, lean_object* v_____do__lift_1462_){
_start:
{
if (lean_obj_tag(v_____do__lift_1462_) == 0)
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1460_);
v___x_1464_ = lean_apply_2(v_toPure_1461_, lean_box(0), v___x_1463_);
return v___x_1464_;
}
else
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_dec(v___x_1460_);
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v_____do__lift_1462_);
v___x_1466_ = lean_apply_2(v_toPure_1461_, lean_box(0), v___x_1465_);
return v___x_1466_;
}
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__2(lean_object* v_f_1467_, lean_object* v_toBind_1468_, lean_object* v___f_1469_, lean_object* v___f_1470_, lean_object* v_x1_1471_, lean_object* v_x2_1472_, lean_object* v_x3_1473_){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = lean_apply_1(v_f_1467_, v_x1_1471_);
lean_inc(v_toBind_1468_);
v___x_1475_ = lean_apply_4(v_toBind_1468_, lean_box(0), lean_box(0), v___x_1474_, v___f_1469_);
v___x_1476_ = lean_apply_4(v_toBind_1468_, lean_box(0), lean_box(0), v___x_1475_, v___f_1470_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed(lean_object* v_f_1477_, lean_object* v_toBind_1478_, lean_object* v___f_1479_, lean_object* v___f_1480_, lean_object* v_x1_1481_, lean_object* v_x2_1482_, lean_object* v_x3_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Std_IterM_findSomeM_x3f___redArg___lam__2(v_f_1477_, v_toBind_1478_, v___f_1479_, v___f_1480_, v_x1_1481_, v_x2_1482_, v_x3_1483_);
lean_dec(v_x3_1483_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___redArg(lean_object* v_inst_1485_, lean_object* v_inst_1486_, lean_object* v_it_1487_, lean_object* v_f_1488_){
_start:
{
lean_object* v_toApplicative_1489_; lean_object* v_toBind_1490_; lean_object* v_toPure_1491_; lean_object* v___f_1492_; lean_object* v___f_1493_; lean_object* v___x_1494_; lean_object* v___f_1495_; lean_object* v___f_1496_; lean_object* v___x_1497_; 
v_toApplicative_1489_ = lean_ctor_get(v_inst_1485_, 0);
lean_inc_ref(v_toApplicative_1489_);
v_toBind_1490_ = lean_ctor_get(v_inst_1485_, 1);
lean_inc_n(v_toBind_1490_, 2);
lean_dec_ref(v_inst_1485_);
v_toPure_1491_ = lean_ctor_get(v_toApplicative_1489_, 1);
lean_inc_n(v_toPure_1491_, 2);
lean_dec_ref(v_toApplicative_1489_);
v___f_1492_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1492_, 0, v_toBind_1490_);
v___f_1493_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1493_, 0, v_toPure_1491_);
v___x_1494_ = lean_box(0);
v___f_1495_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1495_, 0, v___x_1494_);
lean_closure_set(v___f_1495_, 1, v_toPure_1491_);
v___f_1496_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1496_, 0, v_f_1488_);
lean_closure_set(v___f_1496_, 1, v_toBind_1490_);
lean_closure_set(v___f_1496_, 2, v___f_1495_);
lean_closure_set(v___f_1496_, 3, v___f_1493_);
v___x_1497_ = lean_apply_6(v_inst_1486_, v___f_1492_, lean_box(0), lean_box(0), v_it_1487_, v___x_1494_, v___f_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f(lean_object* v_00_u03b1_1498_, lean_object* v_00_u03b2_1499_, lean_object* v_00_u03b3_1500_, lean_object* v_m_1501_, lean_object* v_inst_1502_, lean_object* v_inst_1503_, lean_object* v_inst_1504_, lean_object* v_it_1505_, lean_object* v_f_1506_){
_start:
{
lean_object* v_toApplicative_1507_; lean_object* v_toBind_1508_; lean_object* v_toPure_1509_; lean_object* v___f_1510_; lean_object* v___f_1511_; lean_object* v___x_1512_; lean_object* v___f_1513_; lean_object* v___f_1514_; lean_object* v___x_1515_; 
v_toApplicative_1507_ = lean_ctor_get(v_inst_1502_, 0);
lean_inc_ref(v_toApplicative_1507_);
v_toBind_1508_ = lean_ctor_get(v_inst_1502_, 1);
lean_inc_n(v_toBind_1508_, 2);
lean_dec_ref(v_inst_1502_);
v_toPure_1509_ = lean_ctor_get(v_toApplicative_1507_, 1);
lean_inc_n(v_toPure_1509_, 2);
lean_dec_ref(v_toApplicative_1507_);
v___f_1510_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1510_, 0, v_toBind_1508_);
v___f_1511_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1511_, 0, v_toPure_1509_);
v___x_1512_ = lean_box(0);
v___f_1513_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1513_, 0, v___x_1512_);
lean_closure_set(v___f_1513_, 1, v_toPure_1509_);
v___f_1514_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1514_, 0, v_f_1506_);
lean_closure_set(v___f_1514_, 1, v_toBind_1508_);
lean_closure_set(v___f_1514_, 2, v___f_1513_);
lean_closure_set(v___f_1514_, 3, v___f_1511_);
v___x_1515_ = lean_apply_6(v_inst_1504_, v___f_1510_, lean_box(0), lean_box(0), v_it_1505_, v___x_1512_, v___f_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSomeM_x3f___boxed(lean_object* v_00_u03b1_1516_, lean_object* v_00_u03b2_1517_, lean_object* v_00_u03b3_1518_, lean_object* v_m_1519_, lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_it_1523_, lean_object* v_f_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Std_IterM_findSomeM_x3f(v_00_u03b1_1516_, v_00_u03b2_1517_, v_00_u03b3_1518_, v_m_1519_, v_inst_1520_, v_inst_1521_, v_inst_1522_, v_it_1523_, v_f_1524_);
lean_dec(v_inst_1521_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f___redArg(lean_object* v_inst_1526_, lean_object* v_inst_1527_, lean_object* v_it_1528_, lean_object* v_f_1529_){
_start:
{
lean_object* v_toApplicative_1530_; lean_object* v_toBind_1531_; lean_object* v_toPure_1532_; lean_object* v___f_1533_; lean_object* v___f_1534_; lean_object* v___x_1535_; lean_object* v___f_1536_; lean_object* v___f_1537_; lean_object* v___x_1538_; 
v_toApplicative_1530_ = lean_ctor_get(v_inst_1526_, 0);
lean_inc_ref(v_toApplicative_1530_);
v_toBind_1531_ = lean_ctor_get(v_inst_1526_, 1);
lean_inc_n(v_toBind_1531_, 2);
lean_dec_ref(v_inst_1526_);
v_toPure_1532_ = lean_ctor_get(v_toApplicative_1530_, 1);
lean_inc_n(v_toPure_1532_, 2);
lean_dec_ref(v_toApplicative_1530_);
v___f_1533_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1533_, 0, v_toBind_1531_);
v___f_1534_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1534_, 0, v_toPure_1532_);
v___x_1535_ = lean_box(0);
v___f_1536_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1536_, 0, v___x_1535_);
lean_closure_set(v___f_1536_, 1, v_toPure_1532_);
v___f_1537_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1537_, 0, v_f_1529_);
lean_closure_set(v___f_1537_, 1, v_toBind_1531_);
lean_closure_set(v___f_1537_, 2, v___f_1536_);
lean_closure_set(v___f_1537_, 3, v___f_1534_);
v___x_1538_ = lean_apply_6(v_inst_1527_, v___f_1533_, lean_box(0), lean_box(0), v_it_1528_, v___x_1535_, v___f_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f(lean_object* v_00_u03b1_1539_, lean_object* v_00_u03b2_1540_, lean_object* v_00_u03b3_1541_, lean_object* v_m_1542_, lean_object* v_inst_1543_, lean_object* v_inst_1544_, lean_object* v_inst_1545_, lean_object* v_it_1546_, lean_object* v_f_1547_){
_start:
{
lean_object* v_toApplicative_1548_; lean_object* v_toBind_1549_; lean_object* v_toPure_1550_; lean_object* v___f_1551_; lean_object* v___f_1552_; lean_object* v___x_1553_; lean_object* v___f_1554_; lean_object* v___f_1555_; lean_object* v___x_1556_; 
v_toApplicative_1548_ = lean_ctor_get(v_inst_1543_, 0);
lean_inc_ref(v_toApplicative_1548_);
v_toBind_1549_ = lean_ctor_get(v_inst_1543_, 1);
lean_inc_n(v_toBind_1549_, 2);
lean_dec_ref(v_inst_1543_);
v_toPure_1550_ = lean_ctor_get(v_toApplicative_1548_, 1);
lean_inc_n(v_toPure_1550_, 2);
lean_dec_ref(v_toApplicative_1548_);
v___f_1551_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1551_, 0, v_toBind_1549_);
v___f_1552_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1552_, 0, v_toPure_1550_);
v___x_1553_ = lean_box(0);
v___f_1554_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1554_, 0, v___x_1553_);
lean_closure_set(v___f_1554_, 1, v_toPure_1550_);
v___f_1555_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1555_, 0, v_f_1547_);
lean_closure_set(v___f_1555_, 1, v_toBind_1549_);
lean_closure_set(v___f_1555_, 2, v___f_1554_);
lean_closure_set(v___f_1555_, 3, v___f_1552_);
v___x_1556_ = lean_apply_6(v_inst_1545_, v___f_1551_, lean_box(0), lean_box(0), v_it_1546_, v___x_1553_, v___f_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSomeM_x3f___boxed(lean_object* v_00_u03b1_1557_, lean_object* v_00_u03b2_1558_, lean_object* v_00_u03b3_1559_, lean_object* v_m_1560_, lean_object* v_inst_1561_, lean_object* v_inst_1562_, lean_object* v_inst_1563_, lean_object* v_it_1564_, lean_object* v_f_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Std_IterM_Partial_findSomeM_x3f(v_00_u03b1_1557_, v_00_u03b2_1558_, v_00_u03b3_1559_, v_m_1560_, v_inst_1561_, v_inst_1562_, v_inst_1563_, v_it_1564_, v_f_1565_);
lean_dec(v_inst_1562_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f___redArg(lean_object* v_inst_1567_, lean_object* v_inst_1568_, lean_object* v_it_1569_, lean_object* v_f_1570_){
_start:
{
lean_object* v_toApplicative_1571_; lean_object* v_toBind_1572_; lean_object* v_toPure_1573_; lean_object* v___f_1574_; lean_object* v___f_1575_; lean_object* v___x_1576_; lean_object* v___f_1577_; lean_object* v___f_1578_; lean_object* v___x_1579_; 
v_toApplicative_1571_ = lean_ctor_get(v_inst_1567_, 0);
lean_inc_ref(v_toApplicative_1571_);
v_toBind_1572_ = lean_ctor_get(v_inst_1567_, 1);
lean_inc_n(v_toBind_1572_, 2);
lean_dec_ref(v_inst_1567_);
v_toPure_1573_ = lean_ctor_get(v_toApplicative_1571_, 1);
lean_inc_n(v_toPure_1573_, 2);
lean_dec_ref(v_toApplicative_1571_);
v___f_1574_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1574_, 0, v_toBind_1572_);
v___f_1575_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1575_, 0, v_toPure_1573_);
v___x_1576_ = lean_box(0);
v___f_1577_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1577_, 0, v___x_1576_);
lean_closure_set(v___f_1577_, 1, v_toPure_1573_);
v___f_1578_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1578_, 0, v_f_1570_);
lean_closure_set(v___f_1578_, 1, v_toBind_1572_);
lean_closure_set(v___f_1578_, 2, v___f_1577_);
lean_closure_set(v___f_1578_, 3, v___f_1575_);
v___x_1579_ = lean_apply_6(v_inst_1568_, v___f_1574_, lean_box(0), lean_box(0), v_it_1569_, v___x_1576_, v___f_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f(lean_object* v_00_u03b1_1580_, lean_object* v_00_u03b2_1581_, lean_object* v_00_u03b3_1582_, lean_object* v_m_1583_, lean_object* v_inst_1584_, lean_object* v_inst_1585_, lean_object* v_inst_1586_, lean_object* v_inst_1587_, lean_object* v_it_1588_, lean_object* v_f_1589_){
_start:
{
lean_object* v_toApplicative_1590_; lean_object* v_toBind_1591_; lean_object* v_toPure_1592_; lean_object* v___f_1593_; lean_object* v___f_1594_; lean_object* v___x_1595_; lean_object* v___f_1596_; lean_object* v___f_1597_; lean_object* v___x_1598_; 
v_toApplicative_1590_ = lean_ctor_get(v_inst_1584_, 0);
lean_inc_ref(v_toApplicative_1590_);
v_toBind_1591_ = lean_ctor_get(v_inst_1584_, 1);
lean_inc_n(v_toBind_1591_, 2);
lean_dec_ref(v_inst_1584_);
v_toPure_1592_ = lean_ctor_get(v_toApplicative_1590_, 1);
lean_inc_n(v_toPure_1592_, 2);
lean_dec_ref(v_toApplicative_1590_);
v___f_1593_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1593_, 0, v_toBind_1591_);
v___f_1594_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1594_, 0, v_toPure_1592_);
v___x_1595_ = lean_box(0);
v___f_1596_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1596_, 0, v___x_1595_);
lean_closure_set(v___f_1596_, 1, v_toPure_1592_);
v___f_1597_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1597_, 0, v_f_1589_);
lean_closure_set(v___f_1597_, 1, v_toBind_1591_);
lean_closure_set(v___f_1597_, 2, v___f_1596_);
lean_closure_set(v___f_1597_, 3, v___f_1594_);
v___x_1598_ = lean_apply_6(v_inst_1586_, v___f_1593_, lean_box(0), lean_box(0), v_it_1588_, v___x_1595_, v___f_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSomeM_x3f___boxed(lean_object* v_00_u03b1_1599_, lean_object* v_00_u03b2_1600_, lean_object* v_00_u03b3_1601_, lean_object* v_m_1602_, lean_object* v_inst_1603_, lean_object* v_inst_1604_, lean_object* v_inst_1605_, lean_object* v_inst_1606_, lean_object* v_it_1607_, lean_object* v_f_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Std_IterM_Total_findSomeM_x3f(v_00_u03b1_1599_, v_00_u03b2_1600_, v_00_u03b3_1601_, v_m_1602_, v_inst_1603_, v_inst_1604_, v_inst_1605_, v_inst_1606_, v_it_1607_, v_f_1608_);
lean_dec(v_inst_1604_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg___lam__3(lean_object* v_f_1610_, lean_object* v_toPure_1611_, lean_object* v_toBind_1612_, lean_object* v___f_1613_, lean_object* v___f_1614_, lean_object* v_x1_1615_, lean_object* v_x2_1616_, lean_object* v_x3_1617_){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1618_ = lean_apply_1(v_f_1610_, v_x1_1615_);
v___x_1619_ = lean_apply_2(v_toPure_1611_, lean_box(0), v___x_1618_);
lean_inc(v_toBind_1612_);
v___x_1620_ = lean_apply_4(v_toBind_1612_, lean_box(0), lean_box(0), v___x_1619_, v___f_1613_);
v___x_1621_ = lean_apply_4(v_toBind_1612_, lean_box(0), lean_box(0), v___x_1620_, v___f_1614_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg___lam__3___boxed(lean_object* v_f_1622_, lean_object* v_toPure_1623_, lean_object* v_toBind_1624_, lean_object* v___f_1625_, lean_object* v___f_1626_, lean_object* v_x1_1627_, lean_object* v_x2_1628_, lean_object* v_x3_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Std_IterM_findSome_x3f___redArg___lam__3(v_f_1622_, v_toPure_1623_, v_toBind_1624_, v___f_1625_, v___f_1626_, v_x1_1627_, v_x2_1628_, v_x3_1629_);
lean_dec(v_x3_1629_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___redArg(lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_it_1633_, lean_object* v_f_1634_){
_start:
{
lean_object* v_toApplicative_1635_; lean_object* v_toBind_1636_; lean_object* v_toPure_1637_; lean_object* v___f_1638_; lean_object* v___f_1639_; lean_object* v___x_1640_; lean_object* v___f_1641_; lean_object* v___f_1642_; lean_object* v___x_1643_; 
v_toApplicative_1635_ = lean_ctor_get(v_inst_1631_, 0);
lean_inc_ref(v_toApplicative_1635_);
v_toBind_1636_ = lean_ctor_get(v_inst_1631_, 1);
lean_inc_n(v_toBind_1636_, 2);
lean_dec_ref(v_inst_1631_);
v_toPure_1637_ = lean_ctor_get(v_toApplicative_1635_, 1);
lean_inc_n(v_toPure_1637_, 3);
lean_dec_ref(v_toApplicative_1635_);
v___f_1638_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1638_, 0, v_toBind_1636_);
v___f_1639_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1639_, 0, v_toPure_1637_);
v___x_1640_ = lean_box(0);
v___f_1641_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1641_, 0, v___x_1640_);
lean_closure_set(v___f_1641_, 1, v_toPure_1637_);
v___f_1642_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1642_, 0, v_f_1634_);
lean_closure_set(v___f_1642_, 1, v_toPure_1637_);
lean_closure_set(v___f_1642_, 2, v_toBind_1636_);
lean_closure_set(v___f_1642_, 3, v___f_1641_);
lean_closure_set(v___f_1642_, 4, v___f_1639_);
v___x_1643_ = lean_apply_6(v_inst_1632_, v___f_1638_, lean_box(0), lean_box(0), v_it_1633_, v___x_1640_, v___f_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f(lean_object* v_00_u03b1_1644_, lean_object* v_00_u03b2_1645_, lean_object* v_00_u03b3_1646_, lean_object* v_m_1647_, lean_object* v_inst_1648_, lean_object* v_inst_1649_, lean_object* v_inst_1650_, lean_object* v_it_1651_, lean_object* v_f_1652_){
_start:
{
lean_object* v_toApplicative_1653_; lean_object* v_toBind_1654_; lean_object* v_toPure_1655_; lean_object* v___f_1656_; lean_object* v___f_1657_; lean_object* v___x_1658_; lean_object* v___f_1659_; lean_object* v___f_1660_; lean_object* v___x_1661_; 
v_toApplicative_1653_ = lean_ctor_get(v_inst_1648_, 0);
lean_inc_ref(v_toApplicative_1653_);
v_toBind_1654_ = lean_ctor_get(v_inst_1648_, 1);
lean_inc_n(v_toBind_1654_, 2);
lean_dec_ref(v_inst_1648_);
v_toPure_1655_ = lean_ctor_get(v_toApplicative_1653_, 1);
lean_inc_n(v_toPure_1655_, 3);
lean_dec_ref(v_toApplicative_1653_);
v___f_1656_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1656_, 0, v_toBind_1654_);
v___f_1657_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1657_, 0, v_toPure_1655_);
v___x_1658_ = lean_box(0);
v___f_1659_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1659_, 0, v___x_1658_);
lean_closure_set(v___f_1659_, 1, v_toPure_1655_);
v___f_1660_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1660_, 0, v_f_1652_);
lean_closure_set(v___f_1660_, 1, v_toPure_1655_);
lean_closure_set(v___f_1660_, 2, v_toBind_1654_);
lean_closure_set(v___f_1660_, 3, v___f_1659_);
lean_closure_set(v___f_1660_, 4, v___f_1657_);
v___x_1661_ = lean_apply_6(v_inst_1650_, v___f_1656_, lean_box(0), lean_box(0), v_it_1651_, v___x_1658_, v___f_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findSome_x3f___boxed(lean_object* v_00_u03b1_1662_, lean_object* v_00_u03b2_1663_, lean_object* v_00_u03b3_1664_, lean_object* v_m_1665_, lean_object* v_inst_1666_, lean_object* v_inst_1667_, lean_object* v_inst_1668_, lean_object* v_it_1669_, lean_object* v_f_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Std_IterM_findSome_x3f(v_00_u03b1_1662_, v_00_u03b2_1663_, v_00_u03b3_1664_, v_m_1665_, v_inst_1666_, v_inst_1667_, v_inst_1668_, v_it_1669_, v_f_1670_);
lean_dec(v_inst_1667_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f___redArg(lean_object* v_inst_1672_, lean_object* v_inst_1673_, lean_object* v_it_1674_, lean_object* v_f_1675_){
_start:
{
lean_object* v_toApplicative_1676_; lean_object* v_toBind_1677_; lean_object* v_toPure_1678_; lean_object* v___f_1679_; lean_object* v___f_1680_; lean_object* v___x_1681_; lean_object* v___f_1682_; lean_object* v___f_1683_; lean_object* v___x_1684_; 
v_toApplicative_1676_ = lean_ctor_get(v_inst_1672_, 0);
lean_inc_ref(v_toApplicative_1676_);
v_toBind_1677_ = lean_ctor_get(v_inst_1672_, 1);
lean_inc_n(v_toBind_1677_, 2);
lean_dec_ref(v_inst_1672_);
v_toPure_1678_ = lean_ctor_get(v_toApplicative_1676_, 1);
lean_inc_n(v_toPure_1678_, 3);
lean_dec_ref(v_toApplicative_1676_);
v___f_1679_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1679_, 0, v_toBind_1677_);
v___f_1680_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1680_, 0, v_toPure_1678_);
v___x_1681_ = lean_box(0);
v___f_1682_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1682_, 0, v___x_1681_);
lean_closure_set(v___f_1682_, 1, v_toPure_1678_);
v___f_1683_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1683_, 0, v_f_1675_);
lean_closure_set(v___f_1683_, 1, v_toPure_1678_);
lean_closure_set(v___f_1683_, 2, v_toBind_1677_);
lean_closure_set(v___f_1683_, 3, v___f_1682_);
lean_closure_set(v___f_1683_, 4, v___f_1680_);
v___x_1684_ = lean_apply_6(v_inst_1673_, v___f_1679_, lean_box(0), lean_box(0), v_it_1674_, v___x_1681_, v___f_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f(lean_object* v_00_u03b1_1685_, lean_object* v_00_u03b2_1686_, lean_object* v_00_u03b3_1687_, lean_object* v_m_1688_, lean_object* v_inst_1689_, lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v_it_1692_, lean_object* v_f_1693_){
_start:
{
lean_object* v_toApplicative_1694_; lean_object* v_toBind_1695_; lean_object* v_toPure_1696_; lean_object* v___f_1697_; lean_object* v___f_1698_; lean_object* v___x_1699_; lean_object* v___f_1700_; lean_object* v___f_1701_; lean_object* v___x_1702_; 
v_toApplicative_1694_ = lean_ctor_get(v_inst_1689_, 0);
lean_inc_ref(v_toApplicative_1694_);
v_toBind_1695_ = lean_ctor_get(v_inst_1689_, 1);
lean_inc_n(v_toBind_1695_, 2);
lean_dec_ref(v_inst_1689_);
v_toPure_1696_ = lean_ctor_get(v_toApplicative_1694_, 1);
lean_inc_n(v_toPure_1696_, 3);
lean_dec_ref(v_toApplicative_1694_);
v___f_1697_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1697_, 0, v_toBind_1695_);
v___f_1698_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1698_, 0, v_toPure_1696_);
v___x_1699_ = lean_box(0);
v___f_1700_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1700_, 0, v___x_1699_);
lean_closure_set(v___f_1700_, 1, v_toPure_1696_);
v___f_1701_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1701_, 0, v_f_1693_);
lean_closure_set(v___f_1701_, 1, v_toPure_1696_);
lean_closure_set(v___f_1701_, 2, v_toBind_1695_);
lean_closure_set(v___f_1701_, 3, v___f_1700_);
lean_closure_set(v___f_1701_, 4, v___f_1698_);
v___x_1702_ = lean_apply_6(v_inst_1691_, v___f_1697_, lean_box(0), lean_box(0), v_it_1692_, v___x_1699_, v___f_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findSome_x3f___boxed(lean_object* v_00_u03b1_1703_, lean_object* v_00_u03b2_1704_, lean_object* v_00_u03b3_1705_, lean_object* v_m_1706_, lean_object* v_inst_1707_, lean_object* v_inst_1708_, lean_object* v_inst_1709_, lean_object* v_it_1710_, lean_object* v_f_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Std_IterM_Partial_findSome_x3f(v_00_u03b1_1703_, v_00_u03b2_1704_, v_00_u03b3_1705_, v_m_1706_, v_inst_1707_, v_inst_1708_, v_inst_1709_, v_it_1710_, v_f_1711_);
lean_dec(v_inst_1708_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f___redArg(lean_object* v_inst_1713_, lean_object* v_inst_1714_, lean_object* v_it_1715_, lean_object* v_f_1716_){
_start:
{
lean_object* v_toApplicative_1717_; lean_object* v_toBind_1718_; lean_object* v_toPure_1719_; lean_object* v___f_1720_; lean_object* v___f_1721_; lean_object* v___x_1722_; lean_object* v___f_1723_; lean_object* v___f_1724_; lean_object* v___x_1725_; 
v_toApplicative_1717_ = lean_ctor_get(v_inst_1713_, 0);
lean_inc_ref(v_toApplicative_1717_);
v_toBind_1718_ = lean_ctor_get(v_inst_1713_, 1);
lean_inc_n(v_toBind_1718_, 2);
lean_dec_ref(v_inst_1713_);
v_toPure_1719_ = lean_ctor_get(v_toApplicative_1717_, 1);
lean_inc_n(v_toPure_1719_, 3);
lean_dec_ref(v_toApplicative_1717_);
v___f_1720_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1720_, 0, v_toBind_1718_);
v___f_1721_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1721_, 0, v_toPure_1719_);
v___x_1722_ = lean_box(0);
v___f_1723_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1723_, 0, v___x_1722_);
lean_closure_set(v___f_1723_, 1, v_toPure_1719_);
v___f_1724_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1724_, 0, v_f_1716_);
lean_closure_set(v___f_1724_, 1, v_toPure_1719_);
lean_closure_set(v___f_1724_, 2, v_toBind_1718_);
lean_closure_set(v___f_1724_, 3, v___f_1723_);
lean_closure_set(v___f_1724_, 4, v___f_1721_);
v___x_1725_ = lean_apply_6(v_inst_1714_, v___f_1720_, lean_box(0), lean_box(0), v_it_1715_, v___x_1722_, v___f_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f(lean_object* v_00_u03b1_1726_, lean_object* v_00_u03b2_1727_, lean_object* v_00_u03b3_1728_, lean_object* v_m_1729_, lean_object* v_inst_1730_, lean_object* v_inst_1731_, lean_object* v_inst_1732_, lean_object* v_inst_1733_, lean_object* v_it_1734_, lean_object* v_f_1735_){
_start:
{
lean_object* v_toApplicative_1736_; lean_object* v_toBind_1737_; lean_object* v_toPure_1738_; lean_object* v___f_1739_; lean_object* v___f_1740_; lean_object* v___x_1741_; lean_object* v___f_1742_; lean_object* v___f_1743_; lean_object* v___x_1744_; 
v_toApplicative_1736_ = lean_ctor_get(v_inst_1730_, 0);
lean_inc_ref(v_toApplicative_1736_);
v_toBind_1737_ = lean_ctor_get(v_inst_1730_, 1);
lean_inc_n(v_toBind_1737_, 2);
lean_dec_ref(v_inst_1730_);
v_toPure_1738_ = lean_ctor_get(v_toApplicative_1736_, 1);
lean_inc_n(v_toPure_1738_, 3);
lean_dec_ref(v_toApplicative_1736_);
v___f_1739_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1739_, 0, v_toBind_1737_);
v___f_1740_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1740_, 0, v_toPure_1738_);
v___x_1741_ = lean_box(0);
v___f_1742_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1742_, 0, v___x_1741_);
lean_closure_set(v___f_1742_, 1, v_toPure_1738_);
v___f_1743_ = lean_alloc_closure((void*)(l_Std_IterM_findSome_x3f___redArg___lam__3___boxed), 8, 5);
lean_closure_set(v___f_1743_, 0, v_f_1735_);
lean_closure_set(v___f_1743_, 1, v_toPure_1738_);
lean_closure_set(v___f_1743_, 2, v_toBind_1737_);
lean_closure_set(v___f_1743_, 3, v___f_1742_);
lean_closure_set(v___f_1743_, 4, v___f_1740_);
v___x_1744_ = lean_apply_6(v_inst_1732_, v___f_1739_, lean_box(0), lean_box(0), v_it_1734_, v___x_1741_, v___f_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findSome_x3f___boxed(lean_object* v_00_u03b1_1745_, lean_object* v_00_u03b2_1746_, lean_object* v_00_u03b3_1747_, lean_object* v_m_1748_, lean_object* v_inst_1749_, lean_object* v_inst_1750_, lean_object* v_inst_1751_, lean_object* v_inst_1752_, lean_object* v_it_1753_, lean_object* v_f_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Std_IterM_Total_findSome_x3f(v_00_u03b1_1745_, v_00_u03b2_1746_, v_00_u03b3_1747_, v_m_1748_, v_inst_1749_, v_inst_1750_, v_inst_1751_, v_inst_1752_, v_it_1753_, v_f_1754_);
lean_dec(v_inst_1750_);
return v_res_1755_;
}
}
lean_object* l_Std_IterM_findM_x3f___redArg___lam__3(lean_object* v_toPure_1756_, lean_object* v___x_1757_, lean_object* v_x1_1758_, uint8_t v_____do__lift_1759_){
_start:
{
if (v_____do__lift_1759_ == 0)
{
lean_object* v___x_1760_; 
lean_dec(v_x1_1758_);
v___x_1760_ = lean_apply_2(v_toPure_1756_, lean_box(0), v___x_1757_);
return v___x_1760_;
}
else
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
lean_dec(v___x_1757_);
v___x_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1761_, 0, v_x1_1758_);
v___x_1762_ = lean_apply_2(v_toPure_1756_, lean_box(0), v___x_1761_);
return v___x_1762_;
}
}
}
LEAN_EXPORT void l_Std_IterM_findM_x3f___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_1756_ = stack[0].m_obj;
lean_object* v___x_1757_ = stack[1].m_obj;
lean_object* v_x1_1758_ = stack[2].m_obj;
uint8_t v_____do__lift_1759_ = stack[3].m_num;
lean_object* v_res_1763_;
v_res_1763_ = l_Std_IterM_findM_x3f___redArg___lam__3(v_toPure_1756_, v___x_1757_, v_x1_1758_, v_____do__lift_1759_);
stack->m_obj
 = v_res_1763_;
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__3___boxed(lean_object* v_toPure_1764_, lean_object* v___x_1765_, lean_object* v_x1_1766_, lean_object* v_____do__lift_1767_){
_start:
{
uint8_t v_____do__lift_169__boxed_1768_; lean_object* v_res_1769_; 
v_____do__lift_169__boxed_1768_ = lean_unbox(v_____do__lift_1767_);
v_res_1769_ = l_Std_IterM_findM_x3f___redArg___lam__3(v_toPure_1764_, v___x_1765_, v_x1_1766_, v_____do__lift_169__boxed_1768_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__0(lean_object* v_toPure_1770_, lean_object* v___x_1771_, lean_object* v_f_1772_, lean_object* v_toBind_1773_, lean_object* v___f_1774_, lean_object* v___f_1775_, lean_object* v_x1_1776_, lean_object* v_x2_1777_, lean_object* v_x3_1778_){
_start:
{
lean_object* v___f_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_inc(v_x1_1776_);
v___f_1779_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_1779_, 0, v_toPure_1770_);
lean_closure_set(v___f_1779_, 1, v___x_1771_);
lean_closure_set(v___f_1779_, 2, v_x1_1776_);
v___x_1780_ = lean_apply_1(v_f_1772_, v_x1_1776_);
lean_inc_n(v_toBind_1773_, 2);
v___x_1781_ = lean_apply_4(v_toBind_1773_, lean_box(0), lean_box(0), v___x_1780_, v___f_1779_);
v___x_1782_ = lean_apply_4(v_toBind_1773_, lean_box(0), lean_box(0), v___x_1781_, v___f_1774_);
v___x_1783_ = lean_apply_4(v_toBind_1773_, lean_box(0), lean_box(0), v___x_1782_, v___f_1775_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_1784_, lean_object* v___x_1785_, lean_object* v_f_1786_, lean_object* v_toBind_1787_, lean_object* v___f_1788_, lean_object* v___f_1789_, lean_object* v_x1_1790_, lean_object* v_x2_1791_, lean_object* v_x3_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Std_IterM_findM_x3f___redArg___lam__0(v_toPure_1784_, v___x_1785_, v_f_1786_, v_toBind_1787_, v___f_1788_, v___f_1789_, v_x1_1790_, v_x2_1791_, v_x3_1792_);
lean_dec(v_x3_1792_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___redArg(lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_it_1796_, lean_object* v_f_1797_){
_start:
{
lean_object* v_toApplicative_1798_; lean_object* v_toBind_1799_; lean_object* v_toPure_1800_; lean_object* v___f_1801_; lean_object* v___f_1802_; lean_object* v___x_1803_; lean_object* v___f_1804_; lean_object* v___f_1805_; lean_object* v___x_1806_; 
v_toApplicative_1798_ = lean_ctor_get(v_inst_1794_, 0);
lean_inc_ref(v_toApplicative_1798_);
v_toBind_1799_ = lean_ctor_get(v_inst_1794_, 1);
lean_inc_n(v_toBind_1799_, 2);
lean_dec_ref(v_inst_1794_);
v_toPure_1800_ = lean_ctor_get(v_toApplicative_1798_, 1);
lean_inc_n(v_toPure_1800_, 3);
lean_dec_ref(v_toApplicative_1798_);
v___f_1801_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1801_, 0, v_toBind_1799_);
v___f_1802_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1802_, 0, v_toPure_1800_);
v___x_1803_ = lean_box(0);
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
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f(lean_object* v_00_u03b1_1807_, lean_object* v_00_u03b2_1808_, lean_object* v_m_1809_, lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_inst_1812_, lean_object* v_it_1813_, lean_object* v_f_1814_){
_start:
{
lean_object* v_toApplicative_1815_; lean_object* v_toBind_1816_; lean_object* v_toPure_1817_; lean_object* v___f_1818_; lean_object* v___f_1819_; lean_object* v___x_1820_; lean_object* v___f_1821_; lean_object* v___f_1822_; lean_object* v___x_1823_; 
v_toApplicative_1815_ = lean_ctor_get(v_inst_1810_, 0);
lean_inc_ref(v_toApplicative_1815_);
v_toBind_1816_ = lean_ctor_get(v_inst_1810_, 1);
lean_inc_n(v_toBind_1816_, 2);
lean_dec_ref(v_inst_1810_);
v_toPure_1817_ = lean_ctor_get(v_toApplicative_1815_, 1);
lean_inc_n(v_toPure_1817_, 3);
lean_dec_ref(v_toApplicative_1815_);
v___f_1818_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1818_, 0, v_toBind_1816_);
v___f_1819_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1819_, 0, v_toPure_1817_);
v___x_1820_ = lean_box(0);
v___f_1821_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1821_, 0, v___x_1820_);
lean_closure_set(v___f_1821_, 1, v_toPure_1817_);
v___f_1822_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1822_, 0, v_toPure_1817_);
lean_closure_set(v___f_1822_, 1, v___x_1820_);
lean_closure_set(v___f_1822_, 2, v_f_1814_);
lean_closure_set(v___f_1822_, 3, v_toBind_1816_);
lean_closure_set(v___f_1822_, 4, v___f_1821_);
lean_closure_set(v___f_1822_, 5, v___f_1819_);
v___x_1823_ = lean_apply_6(v_inst_1812_, v___f_1818_, lean_box(0), lean_box(0), v_it_1813_, v___x_1820_, v___f_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_findM_x3f___boxed(lean_object* v_00_u03b1_1824_, lean_object* v_00_u03b2_1825_, lean_object* v_m_1826_, lean_object* v_inst_1827_, lean_object* v_inst_1828_, lean_object* v_inst_1829_, lean_object* v_it_1830_, lean_object* v_f_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Std_IterM_findM_x3f(v_00_u03b1_1824_, v_00_u03b2_1825_, v_m_1826_, v_inst_1827_, v_inst_1828_, v_inst_1829_, v_it_1830_, v_f_1831_);
lean_dec(v_inst_1828_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f___redArg(lean_object* v_inst_1833_, lean_object* v_inst_1834_, lean_object* v_it_1835_, lean_object* v_f_1836_){
_start:
{
lean_object* v_toApplicative_1837_; lean_object* v_toBind_1838_; lean_object* v_toPure_1839_; lean_object* v___f_1840_; lean_object* v___f_1841_; lean_object* v___x_1842_; lean_object* v___f_1843_; lean_object* v___f_1844_; lean_object* v___x_1845_; 
v_toApplicative_1837_ = lean_ctor_get(v_inst_1833_, 0);
lean_inc_ref(v_toApplicative_1837_);
v_toBind_1838_ = lean_ctor_get(v_inst_1833_, 1);
lean_inc_n(v_toBind_1838_, 2);
lean_dec_ref(v_inst_1833_);
v_toPure_1839_ = lean_ctor_get(v_toApplicative_1837_, 1);
lean_inc_n(v_toPure_1839_, 3);
lean_dec_ref(v_toApplicative_1837_);
v___f_1840_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1840_, 0, v_toBind_1838_);
v___f_1841_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1841_, 0, v_toPure_1839_);
v___x_1842_ = lean_box(0);
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
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f(lean_object* v_00_u03b1_1846_, lean_object* v_00_u03b2_1847_, lean_object* v_m_1848_, lean_object* v_inst_1849_, lean_object* v_inst_1850_, lean_object* v_inst_1851_, lean_object* v_it_1852_, lean_object* v_f_1853_){
_start:
{
lean_object* v_toApplicative_1854_; lean_object* v_toBind_1855_; lean_object* v_toPure_1856_; lean_object* v___f_1857_; lean_object* v___f_1858_; lean_object* v___x_1859_; lean_object* v___f_1860_; lean_object* v___f_1861_; lean_object* v___x_1862_; 
v_toApplicative_1854_ = lean_ctor_get(v_inst_1849_, 0);
lean_inc_ref(v_toApplicative_1854_);
v_toBind_1855_ = lean_ctor_get(v_inst_1849_, 1);
lean_inc_n(v_toBind_1855_, 2);
lean_dec_ref(v_inst_1849_);
v_toPure_1856_ = lean_ctor_get(v_toApplicative_1854_, 1);
lean_inc_n(v_toPure_1856_, 3);
lean_dec_ref(v_toApplicative_1854_);
v___f_1857_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1857_, 0, v_toBind_1855_);
v___f_1858_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1858_, 0, v_toPure_1856_);
v___x_1859_ = lean_box(0);
v___f_1860_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1860_, 0, v___x_1859_);
lean_closure_set(v___f_1860_, 1, v_toPure_1856_);
v___f_1861_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1861_, 0, v_toPure_1856_);
lean_closure_set(v___f_1861_, 1, v___x_1859_);
lean_closure_set(v___f_1861_, 2, v_f_1853_);
lean_closure_set(v___f_1861_, 3, v_toBind_1855_);
lean_closure_set(v___f_1861_, 4, v___f_1860_);
lean_closure_set(v___f_1861_, 5, v___f_1858_);
v___x_1862_ = lean_apply_6(v_inst_1851_, v___f_1857_, lean_box(0), lean_box(0), v_it_1852_, v___x_1859_, v___f_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_findM_x3f___boxed(lean_object* v_00_u03b1_1863_, lean_object* v_00_u03b2_1864_, lean_object* v_m_1865_, lean_object* v_inst_1866_, lean_object* v_inst_1867_, lean_object* v_inst_1868_, lean_object* v_it_1869_, lean_object* v_f_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Std_IterM_Partial_findM_x3f(v_00_u03b1_1863_, v_00_u03b2_1864_, v_m_1865_, v_inst_1866_, v_inst_1867_, v_inst_1868_, v_it_1869_, v_f_1870_);
lean_dec(v_inst_1867_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f___redArg(lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_it_1874_, lean_object* v_f_1875_){
_start:
{
lean_object* v_toApplicative_1876_; lean_object* v_toBind_1877_; lean_object* v_toPure_1878_; lean_object* v___f_1879_; lean_object* v___f_1880_; lean_object* v___x_1881_; lean_object* v___f_1882_; lean_object* v___f_1883_; lean_object* v___x_1884_; 
v_toApplicative_1876_ = lean_ctor_get(v_inst_1872_, 0);
lean_inc_ref(v_toApplicative_1876_);
v_toBind_1877_ = lean_ctor_get(v_inst_1872_, 1);
lean_inc_n(v_toBind_1877_, 2);
lean_dec_ref(v_inst_1872_);
v_toPure_1878_ = lean_ctor_get(v_toApplicative_1876_, 1);
lean_inc_n(v_toPure_1878_, 3);
lean_dec_ref(v_toApplicative_1876_);
v___f_1879_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1879_, 0, v_toBind_1877_);
v___f_1880_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1880_, 0, v_toPure_1878_);
v___x_1881_ = lean_box(0);
v___f_1882_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1882_, 0, v___x_1881_);
lean_closure_set(v___f_1882_, 1, v_toPure_1878_);
v___f_1883_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1883_, 0, v_toPure_1878_);
lean_closure_set(v___f_1883_, 1, v___x_1881_);
lean_closure_set(v___f_1883_, 2, v_f_1875_);
lean_closure_set(v___f_1883_, 3, v_toBind_1877_);
lean_closure_set(v___f_1883_, 4, v___f_1882_);
lean_closure_set(v___f_1883_, 5, v___f_1880_);
v___x_1884_ = lean_apply_6(v_inst_1873_, v___f_1879_, lean_box(0), lean_box(0), v_it_1874_, v___x_1881_, v___f_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f(lean_object* v_00_u03b1_1885_, lean_object* v_00_u03b2_1886_, lean_object* v_m_1887_, lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v_inst_1891_, lean_object* v_it_1892_, lean_object* v_f_1893_){
_start:
{
lean_object* v_toApplicative_1894_; lean_object* v_toBind_1895_; lean_object* v_toPure_1896_; lean_object* v___f_1897_; lean_object* v___f_1898_; lean_object* v___x_1899_; lean_object* v___f_1900_; lean_object* v___f_1901_; lean_object* v___x_1902_; 
v_toApplicative_1894_ = lean_ctor_get(v_inst_1888_, 0);
lean_inc_ref(v_toApplicative_1894_);
v_toBind_1895_ = lean_ctor_get(v_inst_1888_, 1);
lean_inc_n(v_toBind_1895_, 2);
lean_dec_ref(v_inst_1888_);
v_toPure_1896_ = lean_ctor_get(v_toApplicative_1894_, 1);
lean_inc_n(v_toPure_1896_, 3);
lean_dec_ref(v_toApplicative_1894_);
v___f_1897_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1897_, 0, v_toBind_1895_);
v___f_1898_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1898_, 0, v_toPure_1896_);
v___x_1899_ = lean_box(0);
v___f_1900_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1900_, 0, v___x_1899_);
lean_closure_set(v___f_1900_, 1, v_toPure_1896_);
v___f_1901_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__0___boxed), 9, 6);
lean_closure_set(v___f_1901_, 0, v_toPure_1896_);
lean_closure_set(v___f_1901_, 1, v___x_1899_);
lean_closure_set(v___f_1901_, 2, v_f_1893_);
lean_closure_set(v___f_1901_, 3, v_toBind_1895_);
lean_closure_set(v___f_1901_, 4, v___f_1900_);
lean_closure_set(v___f_1901_, 5, v___f_1898_);
v___x_1902_ = lean_apply_6(v_inst_1890_, v___f_1897_, lean_box(0), lean_box(0), v_it_1892_, v___x_1899_, v___f_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_findM_x3f___boxed(lean_object* v_00_u03b1_1903_, lean_object* v_00_u03b2_1904_, lean_object* v_m_1905_, lean_object* v_inst_1906_, lean_object* v_inst_1907_, lean_object* v_inst_1908_, lean_object* v_inst_1909_, lean_object* v_it_1910_, lean_object* v_f_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Std_IterM_Total_findM_x3f(v_00_u03b1_1903_, v_00_u03b2_1904_, v_m_1905_, v_inst_1906_, v_inst_1907_, v_inst_1908_, v_inst_1909_, v_it_1910_, v_f_1911_);
lean_dec(v_inst_1907_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg___lam__4(lean_object* v_toPure_1913_, lean_object* v___x_1914_, lean_object* v_f_1915_, lean_object* v_toBind_1916_, lean_object* v___f_1917_, lean_object* v___f_1918_, lean_object* v_x1_1919_, lean_object* v_x2_1920_, lean_object* v_x3_1921_){
_start:
{
lean_object* v___f_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
lean_inc(v_x1_1919_);
lean_inc(v_toPure_1913_);
v___f_1922_ = lean_alloc_closure((void*)(l_Std_IterM_findM_x3f___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_1922_, 0, v_toPure_1913_);
lean_closure_set(v___f_1922_, 1, v___x_1914_);
lean_closure_set(v___f_1922_, 2, v_x1_1919_);
v___x_1923_ = lean_apply_1(v_f_1915_, v_x1_1919_);
v___x_1924_ = lean_apply_2(v_toPure_1913_, lean_box(0), v___x_1923_);
lean_inc_n(v_toBind_1916_, 2);
v___x_1925_ = lean_apply_4(v_toBind_1916_, lean_box(0), lean_box(0), v___x_1924_, v___f_1922_);
v___x_1926_ = lean_apply_4(v_toBind_1916_, lean_box(0), lean_box(0), v___x_1925_, v___f_1917_);
v___x_1927_ = lean_apply_4(v_toBind_1916_, lean_box(0), lean_box(0), v___x_1926_, v___f_1918_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg___lam__4___boxed(lean_object* v_toPure_1928_, lean_object* v___x_1929_, lean_object* v_f_1930_, lean_object* v_toBind_1931_, lean_object* v___f_1932_, lean_object* v___f_1933_, lean_object* v_x1_1934_, lean_object* v_x2_1935_, lean_object* v_x3_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Std_IterM_find_x3f___redArg___lam__4(v_toPure_1928_, v___x_1929_, v_f_1930_, v_toBind_1931_, v___f_1932_, v___f_1933_, v_x1_1934_, v_x2_1935_, v_x3_1936_);
lean_dec(v_x3_1936_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___redArg(lean_object* v_inst_1938_, lean_object* v_inst_1939_, lean_object* v_it_1940_, lean_object* v_f_1941_){
_start:
{
lean_object* v_toApplicative_1942_; lean_object* v_toBind_1943_; lean_object* v_toPure_1944_; lean_object* v___f_1945_; lean_object* v___f_1946_; lean_object* v___x_1947_; lean_object* v___f_1948_; lean_object* v___f_1949_; lean_object* v___x_1950_; 
v_toApplicative_1942_ = lean_ctor_get(v_inst_1938_, 0);
lean_inc_ref(v_toApplicative_1942_);
v_toBind_1943_ = lean_ctor_get(v_inst_1938_, 1);
lean_inc_n(v_toBind_1943_, 2);
lean_dec_ref(v_inst_1938_);
v_toPure_1944_ = lean_ctor_get(v_toApplicative_1942_, 1);
lean_inc_n(v_toPure_1944_, 3);
lean_dec_ref(v_toApplicative_1942_);
v___f_1945_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1945_, 0, v_toBind_1943_);
v___f_1946_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1946_, 0, v_toPure_1944_);
v___x_1947_ = lean_box(0);
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
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f(lean_object* v_00_u03b1_1951_, lean_object* v_00_u03b2_1952_, lean_object* v_m_1953_, lean_object* v_inst_1954_, lean_object* v_inst_1955_, lean_object* v_inst_1956_, lean_object* v_it_1957_, lean_object* v_f_1958_){
_start:
{
lean_object* v_toApplicative_1959_; lean_object* v_toBind_1960_; lean_object* v_toPure_1961_; lean_object* v___f_1962_; lean_object* v___f_1963_; lean_object* v___x_1964_; lean_object* v___f_1965_; lean_object* v___f_1966_; lean_object* v___x_1967_; 
v_toApplicative_1959_ = lean_ctor_get(v_inst_1954_, 0);
lean_inc_ref(v_toApplicative_1959_);
v_toBind_1960_ = lean_ctor_get(v_inst_1954_, 1);
lean_inc_n(v_toBind_1960_, 2);
lean_dec_ref(v_inst_1954_);
v_toPure_1961_ = lean_ctor_get(v_toApplicative_1959_, 1);
lean_inc_n(v_toPure_1961_, 3);
lean_dec_ref(v_toApplicative_1959_);
v___f_1962_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1962_, 0, v_toBind_1960_);
v___f_1963_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1963_, 0, v_toPure_1961_);
v___x_1964_ = lean_box(0);
v___f_1965_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1965_, 0, v___x_1964_);
lean_closure_set(v___f_1965_, 1, v_toPure_1961_);
v___f_1966_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_1966_, 0, v_toPure_1961_);
lean_closure_set(v___f_1966_, 1, v___x_1964_);
lean_closure_set(v___f_1966_, 2, v_f_1958_);
lean_closure_set(v___f_1966_, 3, v_toBind_1960_);
lean_closure_set(v___f_1966_, 4, v___f_1965_);
lean_closure_set(v___f_1966_, 5, v___f_1963_);
v___x_1967_ = lean_apply_6(v_inst_1956_, v___f_1962_, lean_box(0), lean_box(0), v_it_1957_, v___x_1964_, v___f_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_find_x3f___boxed(lean_object* v_00_u03b1_1968_, lean_object* v_00_u03b2_1969_, lean_object* v_m_1970_, lean_object* v_inst_1971_, lean_object* v_inst_1972_, lean_object* v_inst_1973_, lean_object* v_it_1974_, lean_object* v_f_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Std_IterM_find_x3f(v_00_u03b1_1968_, v_00_u03b2_1969_, v_m_1970_, v_inst_1971_, v_inst_1972_, v_inst_1973_, v_it_1974_, v_f_1975_);
lean_dec(v_inst_1972_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f___redArg(lean_object* v_inst_1977_, lean_object* v_inst_1978_, lean_object* v_it_1979_, lean_object* v_f_1980_){
_start:
{
lean_object* v_toApplicative_1981_; lean_object* v_toBind_1982_; lean_object* v_toPure_1983_; lean_object* v___f_1984_; lean_object* v___f_1985_; lean_object* v___x_1986_; lean_object* v___f_1987_; lean_object* v___f_1988_; lean_object* v___x_1989_; 
v_toApplicative_1981_ = lean_ctor_get(v_inst_1977_, 0);
lean_inc_ref(v_toApplicative_1981_);
v_toBind_1982_ = lean_ctor_get(v_inst_1977_, 1);
lean_inc_n(v_toBind_1982_, 2);
lean_dec_ref(v_inst_1977_);
v_toPure_1983_ = lean_ctor_get(v_toApplicative_1981_, 1);
lean_inc_n(v_toPure_1983_, 3);
lean_dec_ref(v_toApplicative_1981_);
v___f_1984_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1984_, 0, v_toBind_1982_);
v___f_1985_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1985_, 0, v_toPure_1983_);
v___x_1986_ = lean_box(0);
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
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f(lean_object* v_00_u03b1_1990_, lean_object* v_00_u03b2_1991_, lean_object* v_m_1992_, lean_object* v_inst_1993_, lean_object* v_inst_1994_, lean_object* v_inst_1995_, lean_object* v_it_1996_, lean_object* v_f_1997_){
_start:
{
lean_object* v_toApplicative_1998_; lean_object* v_toBind_1999_; lean_object* v_toPure_2000_; lean_object* v___f_2001_; lean_object* v___f_2002_; lean_object* v___x_2003_; lean_object* v___f_2004_; lean_object* v___f_2005_; lean_object* v___x_2006_; 
v_toApplicative_1998_ = lean_ctor_get(v_inst_1993_, 0);
lean_inc_ref(v_toApplicative_1998_);
v_toBind_1999_ = lean_ctor_get(v_inst_1993_, 1);
lean_inc_n(v_toBind_1999_, 2);
lean_dec_ref(v_inst_1993_);
v_toPure_2000_ = lean_ctor_get(v_toApplicative_1998_, 1);
lean_inc_n(v_toPure_2000_, 3);
lean_dec_ref(v_toApplicative_1998_);
v___f_2001_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2001_, 0, v_toBind_1999_);
v___f_2002_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2002_, 0, v_toPure_2000_);
v___x_2003_ = lean_box(0);
v___f_2004_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2004_, 0, v___x_2003_);
lean_closure_set(v___f_2004_, 1, v_toPure_2000_);
v___f_2005_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_2005_, 0, v_toPure_2000_);
lean_closure_set(v___f_2005_, 1, v___x_2003_);
lean_closure_set(v___f_2005_, 2, v_f_1997_);
lean_closure_set(v___f_2005_, 3, v_toBind_1999_);
lean_closure_set(v___f_2005_, 4, v___f_2004_);
lean_closure_set(v___f_2005_, 5, v___f_2002_);
v___x_2006_ = lean_apply_6(v_inst_1995_, v___f_2001_, lean_box(0), lean_box(0), v_it_1996_, v___x_2003_, v___f_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_find_x3f___boxed(lean_object* v_00_u03b1_2007_, lean_object* v_00_u03b2_2008_, lean_object* v_m_2009_, lean_object* v_inst_2010_, lean_object* v_inst_2011_, lean_object* v_inst_2012_, lean_object* v_it_2013_, lean_object* v_f_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Std_IterM_Partial_find_x3f(v_00_u03b1_2007_, v_00_u03b2_2008_, v_m_2009_, v_inst_2010_, v_inst_2011_, v_inst_2012_, v_it_2013_, v_f_2014_);
lean_dec(v_inst_2011_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f___redArg(lean_object* v_inst_2016_, lean_object* v_inst_2017_, lean_object* v_it_2018_, lean_object* v_f_2019_){
_start:
{
lean_object* v_toApplicative_2020_; lean_object* v_toBind_2021_; lean_object* v_toPure_2022_; lean_object* v___f_2023_; lean_object* v___f_2024_; lean_object* v___x_2025_; lean_object* v___f_2026_; lean_object* v___f_2027_; lean_object* v___x_2028_; 
v_toApplicative_2020_ = lean_ctor_get(v_inst_2016_, 0);
lean_inc_ref(v_toApplicative_2020_);
v_toBind_2021_ = lean_ctor_get(v_inst_2016_, 1);
lean_inc_n(v_toBind_2021_, 2);
lean_dec_ref(v_inst_2016_);
v_toPure_2022_ = lean_ctor_get(v_toApplicative_2020_, 1);
lean_inc_n(v_toPure_2022_, 3);
lean_dec_ref(v_toApplicative_2020_);
v___f_2023_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2023_, 0, v_toBind_2021_);
v___f_2024_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2024_, 0, v_toPure_2022_);
v___x_2025_ = lean_box(0);
v___f_2026_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2026_, 0, v___x_2025_);
lean_closure_set(v___f_2026_, 1, v_toPure_2022_);
v___f_2027_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_2027_, 0, v_toPure_2022_);
lean_closure_set(v___f_2027_, 1, v___x_2025_);
lean_closure_set(v___f_2027_, 2, v_f_2019_);
lean_closure_set(v___f_2027_, 3, v_toBind_2021_);
lean_closure_set(v___f_2027_, 4, v___f_2026_);
lean_closure_set(v___f_2027_, 5, v___f_2024_);
v___x_2028_ = lean_apply_6(v_inst_2017_, v___f_2023_, lean_box(0), lean_box(0), v_it_2018_, v___x_2025_, v___f_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f(lean_object* v_00_u03b1_2029_, lean_object* v_00_u03b2_2030_, lean_object* v_m_2031_, lean_object* v_inst_2032_, lean_object* v_inst_2033_, lean_object* v_inst_2034_, lean_object* v_inst_2035_, lean_object* v_it_2036_, lean_object* v_f_2037_){
_start:
{
lean_object* v_toApplicative_2038_; lean_object* v_toBind_2039_; lean_object* v_toPure_2040_; lean_object* v___f_2041_; lean_object* v___f_2042_; lean_object* v___x_2043_; lean_object* v___f_2044_; lean_object* v___f_2045_; lean_object* v___x_2046_; 
v_toApplicative_2038_ = lean_ctor_get(v_inst_2032_, 0);
lean_inc_ref(v_toApplicative_2038_);
v_toBind_2039_ = lean_ctor_get(v_inst_2032_, 1);
lean_inc_n(v_toBind_2039_, 2);
lean_dec_ref(v_inst_2032_);
v_toPure_2040_ = lean_ctor_get(v_toApplicative_2038_, 1);
lean_inc_n(v_toPure_2040_, 3);
lean_dec_ref(v_toApplicative_2038_);
v___f_2041_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2041_, 0, v_toBind_2039_);
v___f_2042_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2042_, 0, v_toPure_2040_);
v___x_2043_ = lean_box(0);
v___f_2044_ = lean_alloc_closure((void*)(l_Std_IterM_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2044_, 0, v___x_2043_);
lean_closure_set(v___f_2044_, 1, v_toPure_2040_);
v___f_2045_ = lean_alloc_closure((void*)(l_Std_IterM_find_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_2045_, 0, v_toPure_2040_);
lean_closure_set(v___f_2045_, 1, v___x_2043_);
lean_closure_set(v___f_2045_, 2, v_f_2037_);
lean_closure_set(v___f_2045_, 3, v_toBind_2039_);
lean_closure_set(v___f_2045_, 4, v___f_2044_);
lean_closure_set(v___f_2045_, 5, v___f_2042_);
v___x_2046_ = lean_apply_6(v_inst_2034_, v___f_2041_, lean_box(0), lean_box(0), v_it_2036_, v___x_2043_, v___f_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_find_x3f___boxed(lean_object* v_00_u03b1_2047_, lean_object* v_00_u03b2_2048_, lean_object* v_m_2049_, lean_object* v_inst_2050_, lean_object* v_inst_2051_, lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_it_2054_, lean_object* v_f_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Std_IterM_Total_find_x3f(v_00_u03b1_2047_, v_00_u03b2_2048_, v_m_2049_, v_inst_2050_, v_inst_2051_, v_inst_2052_, v_inst_2053_, v_it_2054_, v_f_2055_);
lean_dec(v_inst_2051_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg___lam__0(lean_object* v_toBind_2057_, lean_object* v_x_2058_, lean_object* v_x_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = lean_apply_4(v_toBind_2057_, lean_box(0), lean_box(0), v___y_2061_, v___y_2060_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg___lam__1(lean_object* v_toPure_2063_, lean_object* v_b_2064_, lean_object* v_x_2065_, lean_object* v_x_2066_){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2067_, 0, v_b_2064_);
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
v___x_2069_ = lean_apply_2(v_toPure_2063_, lean_box(0), v___x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg___lam__1___boxed(lean_object* v_toPure_2070_, lean_object* v_b_2071_, lean_object* v_x_2072_, lean_object* v_x_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Std_IterM_first_x3f___redArg___lam__1(v_toPure_2070_, v_b_2071_, v_x_2072_, v_x_2073_);
lean_dec(v_x_2073_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___redArg(lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_it_2077_){
_start:
{
lean_object* v_toApplicative_2078_; lean_object* v_toBind_2079_; lean_object* v_toPure_2080_; lean_object* v___f_2081_; lean_object* v___f_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v_toApplicative_2078_ = lean_ctor_get(v_inst_2075_, 0);
lean_inc_ref(v_toApplicative_2078_);
v_toBind_2079_ = lean_ctor_get(v_inst_2075_, 1);
lean_inc(v_toBind_2079_);
lean_dec_ref(v_inst_2075_);
v_toPure_2080_ = lean_ctor_get(v_toApplicative_2078_, 1);
lean_inc(v_toPure_2080_);
lean_dec_ref(v_toApplicative_2078_);
v___f_2081_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2081_, 0, v_toBind_2079_);
v___f_2082_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2082_, 0, v_toPure_2080_);
v___x_2083_ = lean_box(0);
v___x_2084_ = lean_apply_6(v_inst_2076_, v___f_2081_, lean_box(0), lean_box(0), v_it_2077_, v___x_2083_, v___f_2082_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f(lean_object* v_00_u03b1_2085_, lean_object* v_00_u03b2_2086_, lean_object* v_m_2087_, lean_object* v_inst_2088_, lean_object* v_inst_2089_, lean_object* v_inst_2090_, lean_object* v_it_2091_){
_start:
{
lean_object* v_toApplicative_2092_; lean_object* v_toBind_2093_; lean_object* v_toPure_2094_; lean_object* v___f_2095_; lean_object* v___f_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v_toApplicative_2092_ = lean_ctor_get(v_inst_2088_, 0);
lean_inc_ref(v_toApplicative_2092_);
v_toBind_2093_ = lean_ctor_get(v_inst_2088_, 1);
lean_inc(v_toBind_2093_);
lean_dec_ref(v_inst_2088_);
v_toPure_2094_ = lean_ctor_get(v_toApplicative_2092_, 1);
lean_inc(v_toPure_2094_);
lean_dec_ref(v_toApplicative_2092_);
v___f_2095_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2095_, 0, v_toBind_2093_);
v___f_2096_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2096_, 0, v_toPure_2094_);
v___x_2097_ = lean_box(0);
v___x_2098_ = lean_apply_6(v_inst_2090_, v___f_2095_, lean_box(0), lean_box(0), v_it_2091_, v___x_2097_, v___f_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_first_x3f___boxed(lean_object* v_00_u03b1_2099_, lean_object* v_00_u03b2_2100_, lean_object* v_m_2101_, lean_object* v_inst_2102_, lean_object* v_inst_2103_, lean_object* v_inst_2104_, lean_object* v_it_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Std_IterM_first_x3f(v_00_u03b1_2099_, v_00_u03b2_2100_, v_m_2101_, v_inst_2102_, v_inst_2103_, v_inst_2104_, v_it_2105_);
lean_dec(v_inst_2103_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_first_x3f___redArg(lean_object* v_inst_2107_, lean_object* v_inst_2108_, lean_object* v_it_2109_){
_start:
{
lean_object* v_toApplicative_2110_; lean_object* v_toBind_2111_; lean_object* v_toPure_2112_; lean_object* v___f_2113_; lean_object* v___f_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v_toApplicative_2110_ = lean_ctor_get(v_inst_2107_, 0);
lean_inc_ref(v_toApplicative_2110_);
v_toBind_2111_ = lean_ctor_get(v_inst_2107_, 1);
lean_inc(v_toBind_2111_);
lean_dec_ref(v_inst_2107_);
v_toPure_2112_ = lean_ctor_get(v_toApplicative_2110_, 1);
lean_inc(v_toPure_2112_);
lean_dec_ref(v_toApplicative_2110_);
v___f_2113_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2113_, 0, v_toBind_2111_);
v___f_2114_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2114_, 0, v_toPure_2112_);
v___x_2115_ = lean_box(0);
v___x_2116_ = lean_apply_6(v_inst_2108_, v___f_2113_, lean_box(0), lean_box(0), v_it_2109_, v___x_2115_, v___f_2114_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_first_x3f(lean_object* v_00_u03b1_2117_, lean_object* v_00_u03b2_2118_, lean_object* v_m_2119_, lean_object* v_inst_2120_, lean_object* v_inst_2121_, lean_object* v_inst_2122_, lean_object* v_inst_2123_, lean_object* v_it_2124_){
_start:
{
lean_object* v_toApplicative_2125_; lean_object* v_toBind_2126_; lean_object* v_toPure_2127_; lean_object* v___f_2128_; lean_object* v___f_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_toApplicative_2125_ = lean_ctor_get(v_inst_2120_, 0);
lean_inc_ref(v_toApplicative_2125_);
v_toBind_2126_ = lean_ctor_get(v_inst_2120_, 1);
lean_inc(v_toBind_2126_);
lean_dec_ref(v_inst_2120_);
v_toPure_2127_ = lean_ctor_get(v_toApplicative_2125_, 1);
lean_inc(v_toPure_2127_);
lean_dec_ref(v_toApplicative_2125_);
v___f_2128_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2128_, 0, v_toBind_2126_);
v___f_2129_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2129_, 0, v_toPure_2127_);
v___x_2130_ = lean_box(0);
v___x_2131_ = lean_apply_6(v_inst_2122_, v___f_2128_, lean_box(0), lean_box(0), v_it_2124_, v___x_2130_, v___f_2129_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_first_x3f___boxed(lean_object* v_00_u03b1_2132_, lean_object* v_00_u03b2_2133_, lean_object* v_m_2134_, lean_object* v_inst_2135_, lean_object* v_inst_2136_, lean_object* v_inst_2137_, lean_object* v_inst_2138_, lean_object* v_it_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Std_IterM_Total_first_x3f(v_00_u03b1_2132_, v_00_u03b2_2133_, v_m_2134_, v_inst_2135_, v_inst_2136_, v_inst_2137_, v_inst_2138_, v_it_2139_);
lean_dec(v_inst_2136_);
return v_res_2140_;
}
}
lean_object* l_Std_IterM_isEmpty___redArg___lam__1(lean_object* v_toPure_2144_, lean_object* v_x_2145_, lean_object* v_x_2146_, uint8_t v_x_2147_){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = ((lean_object*)(l_Std_IterM_isEmpty___redArg___lam__1___closed__0));
v___x_2149_ = lean_apply_2(v_toPure_2144_, lean_box(0), v___x_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT void l_Std_IterM_isEmpty___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_2144_ = stack[0].m_obj;
lean_object* v_x_2145_ = stack[1].m_obj;
uint8_t v_x_2147_ = stack[3].m_num;
lean_object* v_res_2150_;
v_res_2150_ = l_Std_IterM_isEmpty___redArg___lam__1(v_toPure_2144_, v_x_2145_, lean_box(0), v_x_2147_);
stack->m_obj
 = v_res_2150_;
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___redArg___lam__1___boxed(lean_object* v_toPure_2151_, lean_object* v_x_2152_, lean_object* v_x_2153_, lean_object* v_x_2154_){
_start:
{
uint8_t v_x_79__boxed_2155_; lean_object* v_res_2156_; 
v_x_79__boxed_2155_ = lean_unbox(v_x_2154_);
v_res_2156_ = l_Std_IterM_isEmpty___redArg___lam__1(v_toPure_2151_, v_x_2152_, v_x_2153_, v_x_79__boxed_2155_);
lean_dec(v_x_2152_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___redArg(lean_object* v_inst_2157_, lean_object* v_inst_2158_, lean_object* v_it_2159_){
_start:
{
lean_object* v_toApplicative_2160_; lean_object* v_toBind_2161_; lean_object* v_toPure_2162_; lean_object* v___f_2163_; lean_object* v___f_2164_; uint8_t v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v_toApplicative_2160_ = lean_ctor_get(v_inst_2157_, 0);
lean_inc_ref(v_toApplicative_2160_);
v_toBind_2161_ = lean_ctor_get(v_inst_2157_, 1);
lean_inc(v_toBind_2161_);
lean_dec_ref(v_inst_2157_);
v_toPure_2162_ = lean_ctor_get(v_toApplicative_2160_, 1);
lean_inc(v_toPure_2162_);
lean_dec_ref(v_toApplicative_2160_);
v___f_2163_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2163_, 0, v_toBind_2161_);
v___f_2164_ = lean_alloc_closure((void*)(l_Std_IterM_isEmpty___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2164_, 0, v_toPure_2162_);
v___x_2165_ = 1;
v___x_2166_ = lean_box(v___x_2165_);
v___x_2167_ = lean_apply_6(v_inst_2158_, v___f_2163_, lean_box(0), lean_box(0), v_it_2159_, v___x_2166_, v___f_2164_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty(lean_object* v_00_u03b1_2168_, lean_object* v_00_u03b2_2169_, lean_object* v_m_2170_, lean_object* v_inst_2171_, lean_object* v_inst_2172_, lean_object* v_inst_2173_, lean_object* v_it_2174_){
_start:
{
lean_object* v_toApplicative_2175_; lean_object* v_toBind_2176_; lean_object* v_toPure_2177_; lean_object* v___f_2178_; lean_object* v___f_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v_toApplicative_2175_ = lean_ctor_get(v_inst_2171_, 0);
lean_inc_ref(v_toApplicative_2175_);
v_toBind_2176_ = lean_ctor_get(v_inst_2171_, 1);
lean_inc(v_toBind_2176_);
lean_dec_ref(v_inst_2171_);
v_toPure_2177_ = lean_ctor_get(v_toApplicative_2175_, 1);
lean_inc(v_toPure_2177_);
lean_dec_ref(v_toApplicative_2175_);
v___f_2178_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2178_, 0, v_toBind_2176_);
v___f_2179_ = lean_alloc_closure((void*)(l_Std_IterM_isEmpty___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2179_, 0, v_toPure_2177_);
v___x_2180_ = 1;
v___x_2181_ = lean_box(v___x_2180_);
v___x_2182_ = lean_apply_6(v_inst_2173_, v___f_2178_, lean_box(0), lean_box(0), v_it_2174_, v___x_2181_, v___f_2179_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_isEmpty___boxed(lean_object* v_00_u03b1_2183_, lean_object* v_00_u03b2_2184_, lean_object* v_m_2185_, lean_object* v_inst_2186_, lean_object* v_inst_2187_, lean_object* v_inst_2188_, lean_object* v_it_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Std_IterM_isEmpty(v_00_u03b1_2183_, v_00_u03b2_2184_, v_m_2185_, v_inst_2186_, v_inst_2187_, v_inst_2188_, v_it_2189_);
lean_dec(v_inst_2187_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_isEmpty___redArg(lean_object* v_inst_2191_, lean_object* v_inst_2192_, lean_object* v_it_2193_){
_start:
{
lean_object* v_toApplicative_2194_; lean_object* v_toBind_2195_; lean_object* v_toPure_2196_; lean_object* v___f_2197_; lean_object* v___f_2198_; uint8_t v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v_toApplicative_2194_ = lean_ctor_get(v_inst_2191_, 0);
lean_inc_ref(v_toApplicative_2194_);
v_toBind_2195_ = lean_ctor_get(v_inst_2191_, 1);
lean_inc(v_toBind_2195_);
lean_dec_ref(v_inst_2191_);
v_toPure_2196_ = lean_ctor_get(v_toApplicative_2194_, 1);
lean_inc(v_toPure_2196_);
lean_dec_ref(v_toApplicative_2194_);
v___f_2197_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2197_, 0, v_toBind_2195_);
v___f_2198_ = lean_alloc_closure((void*)(l_Std_IterM_isEmpty___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2198_, 0, v_toPure_2196_);
v___x_2199_ = 1;
v___x_2200_ = lean_box(v___x_2199_);
v___x_2201_ = lean_apply_6(v_inst_2192_, v___f_2197_, lean_box(0), lean_box(0), v_it_2193_, v___x_2200_, v___f_2198_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_isEmpty(lean_object* v_00_u03b1_2202_, lean_object* v_00_u03b2_2203_, lean_object* v_m_2204_, lean_object* v_inst_2205_, lean_object* v_inst_2206_, lean_object* v_inst_2207_, lean_object* v_inst_2208_, lean_object* v_it_2209_){
_start:
{
lean_object* v_toApplicative_2210_; lean_object* v_toBind_2211_; lean_object* v_toPure_2212_; lean_object* v___f_2213_; lean_object* v___f_2214_; uint8_t v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v_toApplicative_2210_ = lean_ctor_get(v_inst_2205_, 0);
lean_inc_ref(v_toApplicative_2210_);
v_toBind_2211_ = lean_ctor_get(v_inst_2205_, 1);
lean_inc(v_toBind_2211_);
lean_dec_ref(v_inst_2205_);
v_toPure_2212_ = lean_ctor_get(v_toApplicative_2210_, 1);
lean_inc(v_toPure_2212_);
lean_dec_ref(v_toApplicative_2210_);
v___f_2213_ = lean_alloc_closure((void*)(l_Std_IterM_first_x3f___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2213_, 0, v_toBind_2211_);
v___f_2214_ = lean_alloc_closure((void*)(l_Std_IterM_isEmpty___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2214_, 0, v_toPure_2212_);
v___x_2215_ = 1;
v___x_2216_ = lean_box(v___x_2215_);
v___x_2217_ = lean_apply_6(v_inst_2207_, v___f_2213_, lean_box(0), lean_box(0), v_it_2209_, v___x_2216_, v___f_2214_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Total_isEmpty___boxed(lean_object* v_00_u03b1_2218_, lean_object* v_00_u03b2_2219_, lean_object* v_m_2220_, lean_object* v_inst_2221_, lean_object* v_inst_2222_, lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_it_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Std_IterM_Total_isEmpty(v_00_u03b1_2218_, v_00_u03b2_2219_, v_m_2220_, v_inst_2221_, v_inst_2222_, v_inst_2223_, v_inst_2224_, v_it_2225_);
lean_dec(v_inst_2222_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg___lam__1(lean_object* v_toPure_2227_, lean_object* v_____do__lift_2228_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_apply_2(v_toPure_2227_, lean_box(0), v_____do__lift_2228_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg___lam__0(lean_object* v_toPure_2230_, lean_object* v_toBind_2231_, lean_object* v___f_2232_, lean_object* v_x1_2233_, lean_object* v_x2_2234_, lean_object* v_x3_2235_){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2236_ = lean_unsigned_to_nat(1u);
v___x_2237_ = lean_nat_add(v_x3_2235_, v___x_2236_);
v___x_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
v___x_2239_ = lean_apply_2(v_toPure_2230_, lean_box(0), v___x_2238_);
v___x_2240_ = lean_apply_4(v_toBind_2231_, lean_box(0), lean_box(0), v___x_2239_, v___f_2232_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg___lam__0___boxed(lean_object* v_toPure_2241_, lean_object* v_toBind_2242_, lean_object* v___f_2243_, lean_object* v_x1_2244_, lean_object* v_x2_2245_, lean_object* v_x3_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Std_IterM_length___redArg___lam__0(v_toPure_2241_, v_toBind_2242_, v___f_2243_, v_x1_2244_, v_x2_2245_, v_x3_2246_);
lean_dec(v_x3_2246_);
lean_dec(v_x1_2244_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___redArg(lean_object* v_inst_2248_, lean_object* v_inst_2249_, lean_object* v_it_2250_){
_start:
{
lean_object* v_toApplicative_2251_; lean_object* v_toBind_2252_; lean_object* v_toPure_2253_; lean_object* v___x_2254_; lean_object* v___f_2255_; lean_object* v___f_2256_; lean_object* v___f_2257_; lean_object* v___x_2258_; 
v_toApplicative_2251_ = lean_ctor_get(v_inst_2249_, 0);
lean_inc_ref(v_toApplicative_2251_);
v_toBind_2252_ = lean_ctor_get(v_inst_2249_, 1);
lean_inc_n(v_toBind_2252_, 2);
lean_dec_ref(v_inst_2249_);
v_toPure_2253_ = lean_ctor_get(v_toApplicative_2251_, 1);
lean_inc_n(v_toPure_2253_, 2);
lean_dec_ref(v_toApplicative_2251_);
v___x_2254_ = lean_unsigned_to_nat(0u);
v___f_2255_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2255_, 0, v_toBind_2252_);
v___f_2256_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2256_, 0, v_toPure_2253_);
v___f_2257_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2257_, 0, v_toPure_2253_);
lean_closure_set(v___f_2257_, 1, v_toBind_2252_);
lean_closure_set(v___f_2257_, 2, v___f_2256_);
v___x_2258_ = lean_apply_6(v_inst_2248_, v___f_2255_, lean_box(0), lean_box(0), v_it_2250_, v___x_2254_, v___f_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length(lean_object* v_00_u03b1_2259_, lean_object* v_m_2260_, lean_object* v_00_u03b2_2261_, lean_object* v_inst_2262_, lean_object* v_inst_2263_, lean_object* v_inst_2264_, lean_object* v_it_2265_){
_start:
{
lean_object* v_toApplicative_2266_; lean_object* v_toBind_2267_; lean_object* v_toPure_2268_; lean_object* v___x_2269_; lean_object* v___f_2270_; lean_object* v___f_2271_; lean_object* v___f_2272_; lean_object* v___x_2273_; 
v_toApplicative_2266_ = lean_ctor_get(v_inst_2264_, 0);
lean_inc_ref(v_toApplicative_2266_);
v_toBind_2267_ = lean_ctor_get(v_inst_2264_, 1);
lean_inc_n(v_toBind_2267_, 2);
lean_dec_ref(v_inst_2264_);
v_toPure_2268_ = lean_ctor_get(v_toApplicative_2266_, 1);
lean_inc_n(v_toPure_2268_, 2);
lean_dec_ref(v_toApplicative_2266_);
v___x_2269_ = lean_unsigned_to_nat(0u);
v___f_2270_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2270_, 0, v_toBind_2267_);
v___f_2271_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2271_, 0, v_toPure_2268_);
v___f_2272_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2272_, 0, v_toPure_2268_);
lean_closure_set(v___f_2272_, 1, v_toBind_2267_);
lean_closure_set(v___f_2272_, 2, v___f_2271_);
v___x_2273_ = lean_apply_6(v_inst_2263_, v___f_2270_, lean_box(0), lean_box(0), v_it_2265_, v___x_2269_, v___f_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_length___boxed(lean_object* v_00_u03b1_2274_, lean_object* v_m_2275_, lean_object* v_00_u03b2_2276_, lean_object* v_inst_2277_, lean_object* v_inst_2278_, lean_object* v_inst_2279_, lean_object* v_it_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Std_IterM_length(v_00_u03b1_2274_, v_m_2275_, v_00_u03b2_2276_, v_inst_2277_, v_inst_2278_, v_inst_2279_, v_it_2280_);
lean_dec(v_inst_2277_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_count___redArg(lean_object* v_inst_2282_, lean_object* v_inst_2283_, lean_object* v_it_2284_){
_start:
{
lean_object* v_toApplicative_2285_; lean_object* v_toBind_2286_; lean_object* v_toPure_2287_; lean_object* v___x_2288_; lean_object* v___f_2289_; lean_object* v___f_2290_; lean_object* v___f_2291_; lean_object* v___x_2292_; 
v_toApplicative_2285_ = lean_ctor_get(v_inst_2283_, 0);
lean_inc_ref(v_toApplicative_2285_);
v_toBind_2286_ = lean_ctor_get(v_inst_2283_, 1);
lean_inc_n(v_toBind_2286_, 2);
lean_dec_ref(v_inst_2283_);
v_toPure_2287_ = lean_ctor_get(v_toApplicative_2285_, 1);
lean_inc_n(v_toPure_2287_, 2);
lean_dec_ref(v_toApplicative_2285_);
v___x_2288_ = lean_unsigned_to_nat(0u);
v___f_2289_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2289_, 0, v_toBind_2286_);
v___f_2290_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2290_, 0, v_toPure_2287_);
v___f_2291_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2291_, 0, v_toPure_2287_);
lean_closure_set(v___f_2291_, 1, v_toBind_2286_);
lean_closure_set(v___f_2291_, 2, v___f_2290_);
v___x_2292_ = lean_apply_6(v_inst_2282_, v___f_2289_, lean_box(0), lean_box(0), v_it_2284_, v___x_2288_, v___f_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_count(lean_object* v_00_u03b1_2293_, lean_object* v_m_2294_, lean_object* v_00_u03b2_2295_, lean_object* v_inst_2296_, lean_object* v_inst_2297_, lean_object* v_inst_2298_, lean_object* v_it_2299_){
_start:
{
lean_object* v_toApplicative_2300_; lean_object* v_toBind_2301_; lean_object* v_toPure_2302_; lean_object* v___x_2303_; lean_object* v___f_2304_; lean_object* v___f_2305_; lean_object* v___f_2306_; lean_object* v___x_2307_; 
v_toApplicative_2300_ = lean_ctor_get(v_inst_2298_, 0);
lean_inc_ref(v_toApplicative_2300_);
v_toBind_2301_ = lean_ctor_get(v_inst_2298_, 1);
lean_inc_n(v_toBind_2301_, 2);
lean_dec_ref(v_inst_2298_);
v_toPure_2302_ = lean_ctor_get(v_toApplicative_2300_, 1);
lean_inc_n(v_toPure_2302_, 2);
lean_dec_ref(v_toApplicative_2300_);
v___x_2303_ = lean_unsigned_to_nat(0u);
v___f_2304_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2304_, 0, v_toBind_2301_);
v___f_2305_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2305_, 0, v_toPure_2302_);
v___f_2306_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2306_, 0, v_toPure_2302_);
lean_closure_set(v___f_2306_, 1, v_toBind_2301_);
lean_closure_set(v___f_2306_, 2, v___f_2305_);
v___x_2307_ = lean_apply_6(v_inst_2297_, v___f_2304_, lean_box(0), lean_box(0), v_it_2299_, v___x_2303_, v___f_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_count___boxed(lean_object* v_00_u03b1_2308_, lean_object* v_m_2309_, lean_object* v_00_u03b2_2310_, lean_object* v_inst_2311_, lean_object* v_inst_2312_, lean_object* v_inst_2313_, lean_object* v_it_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Std_IterM_count(v_00_u03b1_2308_, v_m_2309_, v_00_u03b2_2310_, v_inst_2311_, v_inst_2312_, v_inst_2313_, v_it_2314_);
lean_dec(v_inst_2311_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_size___redArg(lean_object* v_inst_2316_, lean_object* v_inst_2317_, lean_object* v_it_2318_){
_start:
{
lean_object* v_toApplicative_2319_; lean_object* v_toBind_2320_; lean_object* v_toPure_2321_; lean_object* v___x_2322_; lean_object* v___f_2323_; lean_object* v___f_2324_; lean_object* v___f_2325_; lean_object* v___x_2326_; 
v_toApplicative_2319_ = lean_ctor_get(v_inst_2317_, 0);
lean_inc_ref(v_toApplicative_2319_);
v_toBind_2320_ = lean_ctor_get(v_inst_2317_, 1);
lean_inc_n(v_toBind_2320_, 2);
lean_dec_ref(v_inst_2317_);
v_toPure_2321_ = lean_ctor_get(v_toApplicative_2319_, 1);
lean_inc_n(v_toPure_2321_, 2);
lean_dec_ref(v_toApplicative_2319_);
v___x_2322_ = lean_unsigned_to_nat(0u);
v___f_2323_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2323_, 0, v_toBind_2320_);
v___f_2324_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2324_, 0, v_toPure_2321_);
v___f_2325_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2325_, 0, v_toPure_2321_);
lean_closure_set(v___f_2325_, 1, v_toBind_2320_);
lean_closure_set(v___f_2325_, 2, v___f_2324_);
v___x_2326_ = lean_apply_6(v_inst_2316_, v___f_2323_, lean_box(0), lean_box(0), v_it_2318_, v___x_2322_, v___f_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_size(lean_object* v_00_u03b1_2327_, lean_object* v_m_2328_, lean_object* v_00_u03b2_2329_, lean_object* v_inst_2330_, lean_object* v_inst_2331_, lean_object* v_inst_2332_, lean_object* v_it_2333_){
_start:
{
lean_object* v_toApplicative_2334_; lean_object* v_toBind_2335_; lean_object* v_toPure_2336_; lean_object* v___x_2337_; lean_object* v___f_2338_; lean_object* v___f_2339_; lean_object* v___f_2340_; lean_object* v___x_2341_; 
v_toApplicative_2334_ = lean_ctor_get(v_inst_2332_, 0);
lean_inc_ref(v_toApplicative_2334_);
v_toBind_2335_ = lean_ctor_get(v_inst_2332_, 1);
lean_inc_n(v_toBind_2335_, 2);
lean_dec_ref(v_inst_2332_);
v_toPure_2336_ = lean_ctor_get(v_toApplicative_2334_, 1);
lean_inc_n(v_toPure_2336_, 2);
lean_dec_ref(v_toApplicative_2334_);
v___x_2337_ = lean_unsigned_to_nat(0u);
v___f_2338_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2338_, 0, v_toBind_2335_);
v___f_2339_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2339_, 0, v_toPure_2336_);
v___f_2340_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2340_, 0, v_toPure_2336_);
lean_closure_set(v___f_2340_, 1, v_toBind_2335_);
lean_closure_set(v___f_2340_, 2, v___f_2339_);
v___x_2341_ = lean_apply_6(v_inst_2331_, v___f_2338_, lean_box(0), lean_box(0), v_it_2333_, v___x_2337_, v___f_2340_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_size___boxed(lean_object* v_00_u03b1_2342_, lean_object* v_m_2343_, lean_object* v_00_u03b2_2344_, lean_object* v_inst_2345_, lean_object* v_inst_2346_, lean_object* v_inst_2347_, lean_object* v_it_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Std_IterM_size(v_00_u03b1_2342_, v_m_2343_, v_00_u03b2_2344_, v_inst_2345_, v_inst_2346_, v_inst_2347_, v_it_2348_);
lean_dec(v_inst_2345_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count___redArg(lean_object* v_inst_2350_, lean_object* v_inst_2351_, lean_object* v_it_2352_){
_start:
{
lean_object* v_toApplicative_2353_; lean_object* v_toBind_2354_; lean_object* v_toPure_2355_; lean_object* v___x_2356_; lean_object* v___f_2357_; lean_object* v___f_2358_; lean_object* v___f_2359_; lean_object* v___x_2360_; 
v_toApplicative_2353_ = lean_ctor_get(v_inst_2351_, 0);
lean_inc_ref(v_toApplicative_2353_);
v_toBind_2354_ = lean_ctor_get(v_inst_2351_, 1);
lean_inc_n(v_toBind_2354_, 2);
lean_dec_ref(v_inst_2351_);
v_toPure_2355_ = lean_ctor_get(v_toApplicative_2353_, 1);
lean_inc_n(v_toPure_2355_, 2);
lean_dec_ref(v_toApplicative_2353_);
v___x_2356_ = lean_unsigned_to_nat(0u);
v___f_2357_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2357_, 0, v_toBind_2354_);
v___f_2358_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2358_, 0, v_toPure_2355_);
v___f_2359_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2359_, 0, v_toPure_2355_);
lean_closure_set(v___f_2359_, 1, v_toBind_2354_);
lean_closure_set(v___f_2359_, 2, v___f_2358_);
v___x_2360_ = lean_apply_6(v_inst_2350_, v___f_2357_, lean_box(0), lean_box(0), v_it_2352_, v___x_2356_, v___f_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count(lean_object* v_00_u03b1_2361_, lean_object* v_m_2362_, lean_object* v_00_u03b2_2363_, lean_object* v_inst_2364_, lean_object* v_inst_2365_, lean_object* v_inst_2366_, lean_object* v_it_2367_){
_start:
{
lean_object* v_toApplicative_2368_; lean_object* v_toBind_2369_; lean_object* v_toPure_2370_; lean_object* v___x_2371_; lean_object* v___f_2372_; lean_object* v___f_2373_; lean_object* v___f_2374_; lean_object* v___x_2375_; 
v_toApplicative_2368_ = lean_ctor_get(v_inst_2366_, 0);
lean_inc_ref(v_toApplicative_2368_);
v_toBind_2369_ = lean_ctor_get(v_inst_2366_, 1);
lean_inc_n(v_toBind_2369_, 2);
lean_dec_ref(v_inst_2366_);
v_toPure_2370_ = lean_ctor_get(v_toApplicative_2368_, 1);
lean_inc_n(v_toPure_2370_, 2);
lean_dec_ref(v_toApplicative_2368_);
v___x_2371_ = lean_unsigned_to_nat(0u);
v___f_2372_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2372_, 0, v_toBind_2369_);
v___f_2373_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2373_, 0, v_toPure_2370_);
v___f_2374_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2374_, 0, v_toPure_2370_);
lean_closure_set(v___f_2374_, 1, v_toBind_2369_);
lean_closure_set(v___f_2374_, 2, v___f_2373_);
v___x_2375_ = lean_apply_6(v_inst_2365_, v___f_2372_, lean_box(0), lean_box(0), v_it_2367_, v___x_2371_, v___f_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_count___boxed(lean_object* v_00_u03b1_2376_, lean_object* v_m_2377_, lean_object* v_00_u03b2_2378_, lean_object* v_inst_2379_, lean_object* v_inst_2380_, lean_object* v_inst_2381_, lean_object* v_it_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Std_IterM_Partial_count(v_00_u03b1_2376_, v_m_2377_, v_00_u03b2_2378_, v_inst_2379_, v_inst_2380_, v_inst_2381_, v_it_2382_);
lean_dec(v_inst_2379_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size___redArg(lean_object* v_inst_2384_, lean_object* v_inst_2385_, lean_object* v_it_2386_){
_start:
{
lean_object* v_toApplicative_2387_; lean_object* v_toBind_2388_; lean_object* v_toPure_2389_; lean_object* v___x_2390_; lean_object* v___f_2391_; lean_object* v___f_2392_; lean_object* v___f_2393_; lean_object* v___x_2394_; 
v_toApplicative_2387_ = lean_ctor_get(v_inst_2385_, 0);
lean_inc_ref(v_toApplicative_2387_);
v_toBind_2388_ = lean_ctor_get(v_inst_2385_, 1);
lean_inc_n(v_toBind_2388_, 2);
lean_dec_ref(v_inst_2385_);
v_toPure_2389_ = lean_ctor_get(v_toApplicative_2387_, 1);
lean_inc_n(v_toPure_2389_, 2);
lean_dec_ref(v_toApplicative_2387_);
v___x_2390_ = lean_unsigned_to_nat(0u);
v___f_2391_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2391_, 0, v_toBind_2388_);
v___f_2392_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2392_, 0, v_toPure_2389_);
v___f_2393_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2393_, 0, v_toPure_2389_);
lean_closure_set(v___f_2393_, 1, v_toBind_2388_);
lean_closure_set(v___f_2393_, 2, v___f_2392_);
v___x_2394_ = lean_apply_6(v_inst_2384_, v___f_2391_, lean_box(0), lean_box(0), v_it_2386_, v___x_2390_, v___f_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size(lean_object* v_00_u03b1_2395_, lean_object* v_m_2396_, lean_object* v_00_u03b2_2397_, lean_object* v_inst_2398_, lean_object* v_inst_2399_, lean_object* v_inst_2400_, lean_object* v_it_2401_){
_start:
{
lean_object* v_toApplicative_2402_; lean_object* v_toBind_2403_; lean_object* v_toPure_2404_; lean_object* v___x_2405_; lean_object* v___f_2406_; lean_object* v___f_2407_; lean_object* v___f_2408_; lean_object* v___x_2409_; 
v_toApplicative_2402_ = lean_ctor_get(v_inst_2400_, 0);
lean_inc_ref(v_toApplicative_2402_);
v_toBind_2403_ = lean_ctor_get(v_inst_2400_, 1);
lean_inc_n(v_toBind_2403_, 2);
lean_dec_ref(v_inst_2400_);
v_toPure_2404_ = lean_ctor_get(v_toApplicative_2402_, 1);
lean_inc_n(v_toPure_2404_, 2);
lean_dec_ref(v_toApplicative_2402_);
v___x_2405_ = lean_unsigned_to_nat(0u);
v___f_2406_ = lean_alloc_closure((void*)(l_Std_IterM_fold___redArg___lam__0), 5, 1);
lean_closure_set(v___f_2406_, 0, v_toBind_2403_);
v___f_2407_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2407_, 0, v_toPure_2404_);
v___f_2408_ = lean_alloc_closure((void*)(l_Std_IterM_length___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2408_, 0, v_toPure_2404_);
lean_closure_set(v___f_2408_, 1, v_toBind_2403_);
lean_closure_set(v___f_2408_, 2, v___f_2407_);
v___x_2409_ = lean_apply_6(v_inst_2399_, v___f_2406_, lean_box(0), lean_box(0), v_it_2401_, v___x_2405_, v___f_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_Partial_size___boxed(lean_object* v_00_u03b1_2410_, lean_object* v_m_2411_, lean_object* v_00_u03b2_2412_, lean_object* v_inst_2413_, lean_object* v_inst_2414_, lean_object* v_inst_2415_, lean_object* v_it_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Std_IterM_Partial_size(v_00_u03b1_2410_, v_m_2411_, v_00_u03b2_2412_, v_inst_2413_, v_inst_2414_, v_inst_2415_, v_it_2416_);
lean_dec(v_inst_2413_);
return v_res_2417_;
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
