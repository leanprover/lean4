// Lean compiler output
// Module: Lean.Meta.Match.MatcherApp.Transform
// Imports: Lean.Meta.Match Lean.Meta.InferType Lean.Meta.Check Lean.Meta.Tactic.Split
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1(uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__71___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logInfo___at___Lean_Meta_reportDiag_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__9(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__5___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__0;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___boxed(lean_object**);
lean_object* l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7___boxed(lean_object**);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__4;
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed(lean_object**);
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62___boxed(lean_object**);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__0;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__0;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_MatcherApp_addArg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMPR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___boxed(lean_object**);
lean_object* l_Lean_Meta_arrowDomainsN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__68___boxed(lean_object**);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__7(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_arrowDomainsN_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRev___at___Nat_foldRev___at___Lean_LocalContext_mkLambda_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Iterators_instIteratorMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__66(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__2;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__67___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_MatcherApp_addArg_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Iterators_Types_Attach_instIterator___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed(lean_object**);
lean_object* l_Lean_MVarId_admit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed(lean_object**);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5___boxed(lean_object**);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__0;
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__3___boxed(lean_object**);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed(lean_object**);
lean_object* l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed(lean_object**);
lean_object* l_Lean_Meta_Match_getEquationsFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__9;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__5;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed(lean_object**);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logError___at___Lean_inferDefEqAttr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrowN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__71(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_MatcherApp_addArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__72___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1___closed__1;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PRange_instUpwardEnumerableNat;
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Split_simpMatchTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__7;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__69(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx_x27___at_____private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___Lean_Meta_introNCore_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3;
lean_object* l_Lean_mkArrow___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__67(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forIn_x27Unsafe_loop___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
static lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__0;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__66___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed(lean_object**);
extern lean_object* l_Lean_levelOne;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1(uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3___boxed(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__1;
lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__8;
lean_object* l_Std_PRange_instIteratorRangeIteratorIdOfUpwardEnumerableOfSupportsUpperBound___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__68(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_MatcherApp_addArg_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed(lean_object**);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__72(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = 0;
x_14 = 1;
lean_inc_ref(x_6);
x_15 = l_Lean_Meta_mkLambdaFVars(x_6, x_1, x_13, x_2, x_13, x_2, x_14, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
if (x_4 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = l_Lean_instInhabitedExpr;
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_array_get(x_39, x_6, x_40);
lean_dec_ref(x_6);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_42 = lean_infer_type(x_41, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_45 = l_Lean_Meta_isExprDefEq(x_5, x_43, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec_ref(x_45);
x_18 = x_2;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = x_48;
goto block_38;
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec_ref(x_45);
x_18 = x_4;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = x_49;
goto block_38;
}
}
else
{
uint8_t x_50; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_45, 0);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_45);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_54 = !lean_is_exclusive(x_42);
if (x_54 == 0)
{
return x_42;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_42, 0);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_42);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_18 = x_4;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_11;
x_23 = x_17;
goto block_38;
}
block_38:
{
lean_object* x_24; 
x_24 = l_Lean_Meta_mkLambdaFVars(x_3, x_16, x_13, x_2, x_13, x_2, x_14, x_19, x_20, x_21, x_22, x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_box(x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_box(x_18);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_24);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_58 = !lean_is_exclusive(x_15);
if (x_58 == 0)
{
return x_15;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_15, 0);
x_60 = lean_ctor_get(x_15, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_15);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected matcher application, insufficient number of parameters in alternative", 80, 80);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_26; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_26 = l_Lean_Meta_instantiateLambda(x_4, x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_26) == 0)
{
x_12 = x_26;
goto block_25;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_33; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_33 = l_Lean_Exception_isInterrupt(x_27);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Exception_isRuntime(x_27);
lean_dec(x_27);
x_29 = x_34;
goto block_32;
}
else
{
lean_dec(x_27);
x_29 = x_33;
goto block_32;
}
block_32:
{
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_26);
x_30 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2;
x_31 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_30, x_7, x_8, x_9, x_10, x_28);
x_12 = x_31;
goto block_25;
}
else
{
lean_dec(x_28);
x_12 = x_26;
goto block_25;
}
}
}
block_25:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_box(x_1);
x_16 = lean_box(x_2);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed), 12, 5);
lean_closure_set(x_17, 0, x_13);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_5);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_3);
x_18 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0;
x_19 = 0;
x_20 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_6, x_18, x_17, x_19, x_19, x_7, x_8, x_9, x_10, x_14);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to add argument to matcher application, argument type was not refined by `casesOn`", 89, 89);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected type at MatcherApp.addArg", 36, 36);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_6, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (x_5 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_14 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1;
x_15 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_18 = l_Lean_Meta_whnfD(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 7)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_19, 2);
lean_inc_ref(x_22);
lean_dec(x_19);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_fget(x_4, x_6);
x_25 = lean_box(x_13);
x_26 = lean_box(x_5);
lean_inc_ref(x_1);
x_27 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed), 11, 4);
lean_closure_set(x_27, 0, x_25);
lean_closure_set(x_27, 1, x_26);
lean_closure_set(x_27, 2, x_1);
lean_closure_set(x_27, 3, x_24);
x_28 = lean_array_get(x_23, x_3, x_6);
lean_inc(x_28);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_31 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_21, x_29, x_27, x_30, x_30, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_expr_instantiate1(x_22, x_34);
lean_dec_ref(x_22);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_28, x_37);
lean_dec(x_28);
x_39 = lean_array_set(x_3, x_6, x_38);
x_40 = lean_array_fset(x_4, x_6, x_34);
x_41 = lean_nat_add(x_6, x_37);
lean_dec(x_6);
x_42 = lean_unbox(x_35);
lean_dec(x_35);
x_2 = x_36;
x_3 = x_39;
x_4 = x_40;
x_5 = x_42;
x_6 = x_41;
x_11 = x_33;
goto _start;
}
else
{
uint8_t x_44; 
lean_dec(x_28);
lean_dec_ref(x_22);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_31, 0);
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_31);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_48 = lean_ctor_get(x_18, 1);
lean_inc(x_48);
lean_dec_ref(x_18);
x_49 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3;
x_50 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_49, x_7, x_8, x_9, x_10, x_48);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_51 = !lean_is_exclusive(x_18);
if (x_51 == 0)
{
return x_18;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_18, 0);
x_53 = lean_ctor_get(x_18, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_18);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
x_14 = lean_unbox(x_4);
x_15 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(x_1, x_13, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox(x_2);
x_14 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
x_13 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_MatcherApp_addArg_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_3);
x_7 = l_Lean_Expr_isFVar(x_6);
if (x_7 == 0)
{
lean_dec_ref(x_6);
lean_inc_ref(x_5);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_instInhabitedExpr;
x_9 = lean_array_get(x_8, x_2, x_3);
x_10 = l_Lean_Expr_replaceFVar(x_5, x_6, x_9);
lean_dec_ref(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_MatcherApp_addArg_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_inc_ref(x_4);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(l_Nat_foldRev___at___Lean_Meta_MatcherApp_addArg_spec__0___lam__0___boxed), 5, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
x_10 = l_Nat_foldRev___at___Lean_Meta_MatcherApp_addArg_spec__0___lam__0(x_1, x_2, x_9, lean_box(0), x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_11 = l_Nat_foldRev___at___Nat_foldRev___at___Lean_LocalContext_mkLambda_spec__0_spec__0(x_7, x_9, x_10);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to add argument to matcher application, type error when constructing the new motive", 90, 90);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected matcher application, motive must be lambda expression with #", 71, 71);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" arguments", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_array_get_size(x_11);
x_96 = lean_array_get_size(x_2);
x_97 = lean_nat_dec_eq(x_95, x_96);
lean_dec(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_98 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4;
x_99 = l_Nat_reprFast(x_96);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = l_Lean_MessageData_ofFormat(x_100);
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6;
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_104, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
return x_105;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_105);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
else
{
lean_object* x_110; 
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_1);
x_110 = lean_infer_type(x_1, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec_ref(x_110);
lean_inc_ref(x_11);
lean_inc_ref(x_2);
x_113 = l_Nat_foldRev___at___Lean_Meta_MatcherApp_addArg_spec__0(x_2, x_11, x_96, x_111);
lean_dec(x_96);
x_114 = l_Lean_mkArrow___redArg(x_113, x_12, x_16, x_112);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec_ref(x_114);
x_18 = x_4;
x_19 = x_3;
x_20 = x_111;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_2;
x_25 = x_115;
x_26 = x_8;
x_27 = x_9;
x_28 = x_10;
x_29 = x_13;
x_30 = x_14;
x_31 = x_15;
x_32 = x_16;
x_33 = x_116;
goto block_94;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
lean_dec_ref(x_114);
x_119 = lean_ctor_get(x_3, 0);
lean_inc(x_119);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_117);
x_120 = l_Lean_Meta_getLevel(x_117, x_13, x_14, x_15, x_16, x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec_ref(x_120);
x_123 = lean_array_set(x_10, x_119, x_121);
lean_dec(x_119);
x_18 = x_4;
x_19 = x_3;
x_20 = x_111;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_2;
x_25 = x_117;
x_26 = x_8;
x_27 = x_9;
x_28 = x_123;
x_29 = x_13;
x_30 = x_14;
x_31 = x_15;
x_32 = x_16;
x_33 = x_122;
goto block_94;
}
else
{
uint8_t x_124; 
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_111);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_124 = !lean_is_exclusive(x_120);
if (x_124 == 0)
{
return x_120;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_120, 0);
x_126 = lean_ctor_get(x_120, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_120);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_96);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_128 = !lean_is_exclusive(x_110);
if (x_128 == 0)
{
return x_110;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_110, 0);
x_130 = lean_ctor_get(x_110, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_110);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
block_94:
{
uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_34 = 0;
x_35 = 1;
x_36 = 1;
x_37 = l_Lean_Meta_mkLambdaFVars(x_11, x_25, x_34, x_35, x_34, x_35, x_36, x_29, x_30, x_31, x_32, x_33);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
lean_inc_ref(x_28);
x_40 = lean_array_to_list(x_28);
lean_inc(x_23);
x_41 = l_Lean_Expr_const___override(x_23, x_40);
x_42 = l_Lean_mkAppN(x_41, x_27);
lean_inc(x_38);
x_43 = l_Lean_Expr_app___override(x_42, x_38);
x_44 = l_Lean_mkAppN(x_43, x_24);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc_ref(x_44);
x_45 = l_Lean_Meta_isTypeCorrect(x_44, x_29, x_30, x_31, x_32, x_39);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec_ref(x_44);
lean_dec(x_38);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_1);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec_ref(x_45);
x_49 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1;
x_50 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_49, x_29, x_30, x_31, x_32, x_48);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
lean_dec_ref(x_45);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc_ref(x_29);
x_56 = lean_infer_type(x_44, x_29, x_30, x_31, x_32, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
x_59 = lean_unsigned_to_nat(0u);
x_60 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(x_20, x_57, x_21, x_18, x_34, x_59, x_29, x_30, x_31, x_32, x_58);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2;
x_66 = lean_array_push(x_65, x_1);
x_67 = l_Array_append___redArg(x_66, x_26);
x_68 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_68, 0, x_23);
lean_ctor_set(x_68, 1, x_28);
lean_ctor_set(x_68, 2, x_19);
lean_ctor_set(x_68, 3, x_22);
lean_ctor_set(x_68, 4, x_27);
lean_ctor_set(x_68, 5, x_38);
lean_ctor_set(x_68, 6, x_24);
lean_ctor_set(x_68, 7, x_63);
lean_ctor_set(x_68, 8, x_64);
lean_ctor_set(x_68, 9, x_67);
lean_ctor_set(x_60, 0, x_68);
return x_60;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_60, 0);
x_70 = lean_ctor_get(x_60, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_60);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2;
x_74 = lean_array_push(x_73, x_1);
x_75 = l_Array_append___redArg(x_74, x_26);
x_76 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_76, 0, x_23);
lean_ctor_set(x_76, 1, x_28);
lean_ctor_set(x_76, 2, x_19);
lean_ctor_set(x_76, 3, x_22);
lean_ctor_set(x_76, 4, x_27);
lean_ctor_set(x_76, 5, x_38);
lean_ctor_set(x_76, 6, x_24);
lean_ctor_set(x_76, 7, x_71);
lean_ctor_set(x_76, 8, x_72);
lean_ctor_set(x_76, 9, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_70);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_38);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_19);
lean_dec_ref(x_1);
x_78 = !lean_is_exclusive(x_60);
if (x_78 == 0)
{
return x_60;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_60, 0);
x_80 = lean_ctor_get(x_60, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_60);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_38);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_1);
x_82 = !lean_is_exclusive(x_56);
if (x_82 == 0)
{
return x_56;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_56, 0);
x_84 = lean_ctor_get(x_56, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_56);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec_ref(x_44);
lean_dec(x_38);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_1);
x_86 = !lean_is_exclusive(x_45);
if (x_86 == 0)
{
return x_45;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_45, 0);
x_88 = lean_ctor_get(x_45, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_45);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_1);
x_90 = !lean_is_exclusive(x_37);
if (x_90 == 0)
{
return x_37;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_37, 0);
x_92 = lean_ctor_get(x_37, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_37);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 8);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_1, 9);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_addArg___lam__0___boxed), 17, 10);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_14);
lean_closure_set(x_18, 2, x_10);
lean_closure_set(x_18, 3, x_16);
lean_closure_set(x_18, 4, x_15);
lean_closure_set(x_18, 5, x_11);
lean_closure_set(x_18, 6, x_8);
lean_closure_set(x_18, 7, x_17);
lean_closure_set(x_18, 8, x_12);
lean_closure_set(x_18, 9, x_9);
x_19 = 0;
x_20 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_13, x_18, x_19, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_MatcherApp_addArg_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldRev___at___Lean_Meta_MatcherApp_addArg_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___Lean_Meta_MatcherApp_addArg_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRev___at___Lean_Meta_MatcherApp_addArg_spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_MatcherApp_addArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec_ref(x_8);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_addArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_23; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
x_23 = l_Lean_Exception_isInterrupt(x_17);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Exception_isRuntime(x_17);
lean_dec(x_17);
x_19 = x_24;
goto block_22;
}
else
{
lean_dec(x_17);
x_19 = x_23;
goto block_22;
}
block_22:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_8);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
else
{
lean_dec(x_18);
return x_8;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_32; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
lean_inc(x_26);
lean_inc(x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_32 = l_Lean_Exception_isInterrupt(x_25);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Exception_isRuntime(x_25);
lean_dec(x_25);
x_28 = x_33;
goto block_31;
}
else
{
lean_dec(x_25);
x_28 = x_32;
goto block_31;
}
block_31:
{
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
else
{
lean_dec(x_26);
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_4, x_11);
if (x_12 == 1)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_4, x_14);
lean_dec(x_4);
x_16 = lean_array_fget(x_1, x_15);
x_17 = lean_box(0);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_18 = l_Lean_Meta_kabstract(x_5, x_16, x_17, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
lean_inc_ref(x_2);
x_21 = lean_array_get(x_2, x_3, x_15);
x_22 = lean_expr_instantiate1(x_19, x_21);
lean_dec_ref(x_21);
lean_dec(x_19);
x_4 = x_15;
x_5 = x_22;
x_10 = x_20;
goto _start;
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec_ref(x_18);
x_4 = x_15;
x_5 = x_24;
x_10 = x_25;
goto _start;
}
else
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(x_1, x_2, x_3, x_5, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to transfer argument through matcher application, alt type must be telescope with #", 90, 90);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_21; uint8_t x_22; 
x_21 = lean_array_get_size(x_5);
x_22 = lean_nat_dec_eq(x_21, x_4);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec_ref(x_5);
x_23 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___closed__1;
x_24 = l_Nat_reprFast(x_4);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_MessageData_ofFormat(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_29, x_7, x_8, x_9, x_10, x_11);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_dec(x_4);
x_12 = x_11;
goto block_20;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Expr_getAppNumArgs(x_6);
x_15 = lean_nat_sub(x_14, x_13);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_15, x_16);
lean_dec(x_15);
x_18 = l_Lean_Expr_getRevArg_x21(x_6, x_17);
x_19 = l_Lean_Meta_mkLambdaFVars(x_5, x_18, x_1, x_2, x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_12);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1(uint8_t x_1, uint8_t x_2, uint8_t x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_array_uget(x_6, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(x_1);
x_18 = lean_box(x_2);
x_19 = lean_box(x_3);
lean_inc(x_15);
x_20 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___boxed), 11, 4);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_19);
lean_closure_set(x_20, 3, x_15);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_15);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_22 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_16, x_21, x_20, x_1, x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_uset(x_6, x_5, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_5, x_27);
x_29 = lean_array_uset(x_26, x_5, x_23);
x_5 = x_28;
x_6 = x_29;
x_11 = x_24;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1(uint8_t x_1, uint8_t x_2, uint8_t x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_array_uget(x_6, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(x_1);
x_18 = lean_box(x_2);
x_19 = lean_box(x_3);
lean_inc(x_15);
x_20 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___boxed), 11, 4);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_19);
lean_closure_set(x_20, 3, x_15);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_15);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_22 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_16, x_21, x_20, x_1, x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_uset(x_6, x_5, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_5, x_27);
x_29 = lean_array_uset(x_26, x_5, x_23);
x_30 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1(x_1, x_2, x_3, x_4, x_28, x_29, x_7, x_8, x_9, x_10, x_24);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_array_size(x_5);
x_13 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_14 = l_Array_mapMUnsafe_map___at___Lean_Meta_arrowDomainsN_spec__2(x_12, x_13, x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Array_zip___redArg(x_1, x_15);
lean_dec(x_15);
x_18 = lean_array_size(x_17);
x_19 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1(x_2, x_3, x_4, x_18, x_13, x_17, x_7, x_8, x_9, x_10, x_16);
return x_19;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to transfer argument through matcher application, type error when constructing the new motive", 100, 100);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to transfer argument through matcher application, motive must be lambda expression with #", 96, 96);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_array_get_size(x_9);
x_69 = lean_array_get_size(x_1);
x_70 = lean_nat_dec_eq(x_68, x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_71 = l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3;
x_72 = l_Nat_reprFast(x_69);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_Lean_MessageData_ofFormat(x_73);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_71);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_77, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
return x_78;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_78);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
lean_object* x_83; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_83 = l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(x_1, x_2, x_9, x_69, x_3, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec_ref(x_83);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_84);
x_86 = l_Lean_Meta_mkEq(x_84, x_84, x_11, x_12, x_13, x_14, x_85);
if (lean_obj_tag(x_86) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec_ref(x_86);
x_16 = x_88;
x_17 = x_87;
x_18 = x_1;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
x_22 = x_11;
x_23 = x_12;
x_24 = x_13;
x_25 = x_14;
goto block_67;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec_ref(x_86);
x_91 = lean_ctor_get(x_5, 0);
x_92 = lean_box(0);
x_93 = lean_array_set(x_8, x_91, x_92);
x_16 = x_90;
x_17 = x_89;
x_18 = x_1;
x_19 = x_6;
x_20 = x_7;
x_21 = x_93;
x_22 = x_11;
x_23 = x_12;
x_24 = x_13;
x_25 = x_14;
goto block_67;
}
}
else
{
uint8_t x_94; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
x_94 = !lean_is_exclusive(x_86);
if (x_94 == 0)
{
return x_86;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_86, 0);
x_96 = lean_ctor_get(x_86, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_86);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
x_98 = !lean_is_exclusive(x_83);
if (x_98 == 0)
{
return x_83;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_83, 0);
x_100 = lean_ctor_get(x_83, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_83);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
block_67:
{
uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_26 = 0;
x_27 = 1;
x_28 = 1;
x_29 = l_Lean_Meta_mkLambdaFVars(x_9, x_17, x_26, x_27, x_26, x_27, x_28, x_22, x_23, x_24, x_25, x_16);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_array_to_list(x_21);
x_33 = l_Lean_Expr_const___override(x_20, x_32);
x_34 = l_Lean_mkAppN(x_33, x_19);
x_35 = l_Lean_Expr_app___override(x_34, x_30);
x_36 = l_Lean_mkAppN(x_35, x_18);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc_ref(x_36);
x_37 = l_Lean_Meta_isTypeCorrect(x_36, x_22, x_23, x_24, x_25, x_31);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
x_40 = lean_box(x_26);
x_41 = lean_box(x_27);
x_42 = lean_box(x_28);
x_43 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed), 11, 4);
lean_closure_set(x_43, 0, x_4);
lean_closure_set(x_43, 1, x_40);
lean_closure_set(x_43, 2, x_41);
lean_closure_set(x_43, 3, x_42);
x_44 = lean_unbox(x_38);
lean_dec(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec_ref(x_43);
lean_dec_ref(x_36);
x_45 = l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1;
x_46 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_45, x_22, x_23, x_24, x_25, x_39);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
return x_46;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_46);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; 
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
x_51 = lean_infer_type(x_36, x_22, x_23, x_24, x_25, x_39);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(x_52, x_43, x_26, x_22, x_23, x_24, x_25, x_53);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec_ref(x_43);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
x_55 = !lean_is_exclusive(x_51);
if (x_55 == 0)
{
return x_51;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_51, 0);
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_51);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec_ref(x_36);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_4);
x_59 = !lean_is_exclusive(x_37);
if (x_59 == 0)
{
return x_37;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_37, 0);
x_61 = lean_ctor_get(x_37, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_37);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_4);
x_63 = !lean_is_exclusive(x_29);
if (x_63 == 0)
{
return x_29;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_29, 0);
x_65 = lean_ctor_get(x_29, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_29);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_14);
lean_dec_ref(x_1);
x_15 = l_Lean_instInhabitedExpr;
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed), 15, 8);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_14);
lean_closure_set(x_16, 4, x_10);
lean_closure_set(x_16, 5, x_11);
lean_closure_set(x_16, 6, x_8);
lean_closure_set(x_16, 7, x_9);
x_17 = 0;
x_18 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_12, x_16, x_17, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox(x_2);
x_14 = lean_unbox(x_3);
x_15 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox(x_2);
x_14 = lean_unbox(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1(x_12, x_13, x_14, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox(x_2);
x_14 = lean_unbox(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1(x_12, x_13, x_14, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
x_13 = lean_unbox(x_3);
x_14 = lean_unbox(x_4);
x_15 = l_Lean_Meta_MatcherApp_refineThrough___lam__0(x_1, x_12, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_MatcherApp_refineThrough___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_10);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_refineThrough(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_23; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
x_23 = l_Lean_Exception_isInterrupt(x_17);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Exception_isRuntime(x_17);
lean_dec(x_17);
x_19 = x_24;
goto block_22;
}
else
{
lean_dec(x_17);
x_19 = x_23;
goto block_22;
}
block_22:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_8);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
else
{
lean_dec(x_18);
return x_8;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_32; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
lean_inc(x_26);
lean_inc(x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_32 = l_Lean_Exception_isInterrupt(x_25);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Exception_isRuntime(x_25);
lean_dec(x_25);
x_28 = x_33;
goto block_31;
}
else
{
lean_dec(x_25);
x_28 = x_32;
goto block_31;
}
block_31:
{
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
else
{
lean_dec(x_26);
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = l_Lean_Expr_fvarId_x21(x_7);
lean_dec(x_7);
x_10 = l_Lean_LocalContext_setUserName(x_4, x_9, x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_9);
x_10 = l_Array_zip___redArg(x_1, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec_ref(x_10);
x_14 = l_Lean_Meta_withLCtx_x27___at_____private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___Lean_Meta_introNCore_spec__0_spec__2___redArg(x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_12, x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec_ref(x_10);
x_16 = l_Lean_Meta_withLCtx_x27___at_____private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___Lean_Meta_introNCore_spec__0_spec__2___redArg(x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_19 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(x_10, x_17, x_18, x_9);
lean_dec_ref(x_10);
x_20 = l_Lean_Meta_withLCtx_x27___at_____private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___Lean_Meta_introNCore_spec__0_spec__2___redArg(x_19, x_3, x_4, x_5, x_6, x_7, x_8);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_4, lean_box(0), x_1);
x_11 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed), 9, 3);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_4);
x_10 = lean_apply_2(x_7, lean_box(0), x_9);
x_11 = lean_apply_1(x_8, lean_box(0));
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_withUserNames___redArg(x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_apply_2(x_1, x_3, x_4);
x_13 = lean_apply_7(x_2, lean_box(0), x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed), 11, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_5);
x_12 = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1), 10, 4);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_5);
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
x_12 = lean_apply_1(x_9, lean_box(0));
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_2, x_3, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_fvarId_x21(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_FVarId_getUserName___boxed), 6, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_array_size(x_3);
x_6 = 0;
x_7 = l_Array_mapMUnsafe_map___redArg(x_1, x_2, x_5, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2;
x_5 = l_Lean_throwError___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_apply_2(x_5, lean_box(0), x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkArrow___redArg(x_1, x_2, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_apply_2(x_5, lean_box(0), x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_Expr_isHEq(x_1);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_array_push(x_2, x_10);
lean_inc(x_5);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed), 6, 5);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
x_13 = lean_box(0);
x_14 = lean_apply_2(x_5, lean_box(0), x_13);
x_15 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_14, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed), 7, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed), 7, 6);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_5);
lean_closure_set(x_10, 5, x_6);
x_11 = lean_apply_2(x_7, lean_box(0), x_9);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11) {
_start:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_mkEqHEq), 7, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
x_13 = lean_apply_2(x_3, lean_box(0), x_12);
x_14 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_13, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_15 = lean_box(0);
x_16 = lean_array_push(x_6, x_15);
lean_inc(x_10);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed), 6, 5);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_7);
lean_closure_set(x_17, 2, x_8);
lean_closure_set(x_17, 3, x_9);
lean_closure_set(x_17, 4, x_10);
x_18 = lean_box(0);
x_19 = lean_apply_2(x_10, lean_box(0), x_18);
x_20 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_19, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
x_18 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 2);
lean_inc(x_20);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_7);
x_23 = lean_apply_2(x_1, lean_box(0), x_22);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_ctor_get(x_12, 2);
lean_dec(x_25);
x_26 = lean_ctor_get(x_12, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_12, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_13, 2);
lean_inc(x_30);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_19, x_31);
lean_inc_ref(x_18);
lean_ctor_set(x_12, 1, x_32);
x_33 = lean_nat_dec_lt(x_29, x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_7);
x_35 = lean_apply_2(x_1, lean_box(0), x_34);
return x_35;
}
else
{
uint8_t x_36; 
lean_free_object(x_11);
lean_free_object(x_7);
lean_free_object(x_8);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_13, 2);
lean_dec(x_37);
x_38 = lean_ctor_get(x_13, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_13, 0);
lean_dec(x_39);
x_40 = lean_nat_add(x_29, x_31);
lean_inc_ref(x_28);
lean_ctor_set(x_13, 1, x_40);
if (x_3 == 0)
{
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_array_fget(x_18, x_19);
lean_dec(x_19);
lean_dec_ref(x_18);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_16);
lean_inc(x_17);
x_49 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9), 8, 7);
lean_closure_set(x_49, 0, x_17);
lean_closure_set(x_49, 1, x_16);
lean_closure_set(x_49, 2, x_12);
lean_closure_set(x_49, 3, x_13);
lean_closure_set(x_49, 4, x_1);
lean_closure_set(x_49, 5, x_2);
lean_closure_set(x_49, 6, x_4);
x_50 = lean_array_fget(x_28, x_29);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_inc(x_2);
lean_inc(x_4);
lean_inc_ref(x_5);
x_51 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed), 11, 10);
lean_closure_set(x_51, 0, x_50);
lean_closure_set(x_51, 1, x_5);
lean_closure_set(x_51, 2, x_4);
lean_closure_set(x_51, 3, x_2);
lean_closure_set(x_51, 4, x_49);
lean_closure_set(x_51, 5, x_16);
lean_closure_set(x_51, 6, x_17);
lean_closure_set(x_51, 7, x_12);
lean_closure_set(x_51, 8, x_13);
lean_closure_set(x_51, 9, x_1);
x_52 = lean_alloc_closure((void*)(l_Lean_Meta_isProof), 6, 1);
lean_closure_set(x_52, 0, x_5);
x_53 = lean_apply_2(x_4, lean_box(0), x_52);
x_54 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_53, x_51);
return x_54;
}
else
{
lean_dec(x_48);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_47;
}
}
block_47:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_box(0);
x_42 = lean_array_push(x_16, x_41);
lean_inc(x_1);
x_43 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed), 6, 5);
lean_closure_set(x_43, 0, x_42);
lean_closure_set(x_43, 1, x_17);
lean_closure_set(x_43, 2, x_12);
lean_closure_set(x_43, 3, x_13);
lean_closure_set(x_43, 4, x_1);
x_44 = lean_box(0);
x_45 = lean_apply_2(x_1, lean_box(0), x_44);
x_46 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_45, x_43);
return x_46;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_13);
x_55 = lean_nat_add(x_29, x_31);
lean_inc_ref(x_28);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_28);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_30);
if (x_3 == 0)
{
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_array_fget(x_18, x_19);
lean_dec(x_19);
lean_dec_ref(x_18);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc_ref(x_56);
lean_inc_ref(x_12);
lean_inc(x_16);
lean_inc(x_17);
x_65 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9), 8, 7);
lean_closure_set(x_65, 0, x_17);
lean_closure_set(x_65, 1, x_16);
lean_closure_set(x_65, 2, x_12);
lean_closure_set(x_65, 3, x_56);
lean_closure_set(x_65, 4, x_1);
lean_closure_set(x_65, 5, x_2);
lean_closure_set(x_65, 6, x_4);
x_66 = lean_array_fget(x_28, x_29);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_inc(x_2);
lean_inc(x_4);
lean_inc_ref(x_5);
x_67 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed), 11, 10);
lean_closure_set(x_67, 0, x_66);
lean_closure_set(x_67, 1, x_5);
lean_closure_set(x_67, 2, x_4);
lean_closure_set(x_67, 3, x_2);
lean_closure_set(x_67, 4, x_65);
lean_closure_set(x_67, 5, x_16);
lean_closure_set(x_67, 6, x_17);
lean_closure_set(x_67, 7, x_12);
lean_closure_set(x_67, 8, x_56);
lean_closure_set(x_67, 9, x_1);
x_68 = lean_alloc_closure((void*)(l_Lean_Meta_isProof), 6, 1);
lean_closure_set(x_68, 0, x_5);
x_69 = lean_apply_2(x_4, lean_box(0), x_68);
x_70 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_69, x_67);
return x_70;
}
else
{
lean_dec(x_64);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_63;
}
}
block_63:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_box(0);
x_58 = lean_array_push(x_16, x_57);
lean_inc(x_1);
x_59 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed), 6, 5);
lean_closure_set(x_59, 0, x_58);
lean_closure_set(x_59, 1, x_17);
lean_closure_set(x_59, 2, x_12);
lean_closure_set(x_59, 3, x_56);
lean_closure_set(x_59, 4, x_1);
x_60 = lean_box(0);
x_61 = lean_apply_2(x_1, lean_box(0), x_60);
x_62 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_61, x_59);
return x_62;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_12);
x_71 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_13, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_13, 2);
lean_inc(x_73);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_add(x_19, x_74);
lean_inc_ref(x_18);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_18);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_76, 2, x_20);
x_77 = lean_nat_dec_lt(x_72, x_73);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_8, 0, x_76);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_7);
x_79 = lean_apply_2(x_1, lean_box(0), x_78);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_free_object(x_11);
lean_free_object(x_7);
lean_free_object(x_8);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 x_80 = x_13;
} else {
 lean_dec_ref(x_13);
 x_80 = lean_box(0);
}
x_81 = lean_nat_add(x_72, x_74);
lean_inc_ref(x_71);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 3, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_71);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_73);
if (x_3 == 0)
{
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_array_fget(x_18, x_19);
lean_dec(x_19);
lean_dec_ref(x_18);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc_ref(x_82);
lean_inc_ref(x_76);
lean_inc(x_16);
lean_inc(x_17);
x_91 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9), 8, 7);
lean_closure_set(x_91, 0, x_17);
lean_closure_set(x_91, 1, x_16);
lean_closure_set(x_91, 2, x_76);
lean_closure_set(x_91, 3, x_82);
lean_closure_set(x_91, 4, x_1);
lean_closure_set(x_91, 5, x_2);
lean_closure_set(x_91, 6, x_4);
x_92 = lean_array_fget(x_71, x_72);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_inc(x_2);
lean_inc(x_4);
lean_inc_ref(x_5);
x_93 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed), 11, 10);
lean_closure_set(x_93, 0, x_92);
lean_closure_set(x_93, 1, x_5);
lean_closure_set(x_93, 2, x_4);
lean_closure_set(x_93, 3, x_2);
lean_closure_set(x_93, 4, x_91);
lean_closure_set(x_93, 5, x_16);
lean_closure_set(x_93, 6, x_17);
lean_closure_set(x_93, 7, x_76);
lean_closure_set(x_93, 8, x_82);
lean_closure_set(x_93, 9, x_1);
x_94 = lean_alloc_closure((void*)(l_Lean_Meta_isProof), 6, 1);
lean_closure_set(x_94, 0, x_5);
x_95 = lean_apply_2(x_4, lean_box(0), x_94);
x_96 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_95, x_93);
return x_96;
}
else
{
lean_dec(x_90);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_89;
}
}
block_89:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_box(0);
x_84 = lean_array_push(x_16, x_83);
lean_inc(x_1);
x_85 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed), 6, 5);
lean_closure_set(x_85, 0, x_84);
lean_closure_set(x_85, 1, x_17);
lean_closure_set(x_85, 2, x_76);
lean_closure_set(x_85, 3, x_82);
lean_closure_set(x_85, 4, x_1);
x_86 = lean_box(0);
x_87 = lean_apply_2(x_1, lean_box(0), x_86);
x_88 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_87, x_85);
return x_88;
}
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_97 = lean_ctor_get(x_11, 0);
x_98 = lean_ctor_get(x_11, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_11);
x_99 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_12, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_12, 2);
lean_inc(x_101);
x_102 = lean_nat_dec_lt(x_100, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_98);
lean_ctor_set(x_8, 1, x_103);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_7);
x_105 = lean_apply_2(x_1, lean_box(0), x_104);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_106 = x_12;
} else {
 lean_dec_ref(x_12);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_13, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_13, 2);
lean_inc(x_109);
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_nat_add(x_100, x_110);
lean_inc_ref(x_99);
if (lean_is_scalar(x_106)) {
 x_112 = lean_alloc_ctor(0, 3, 0);
} else {
 x_112 = x_106;
}
lean_ctor_set(x_112, 0, x_99);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_112, 2, x_101);
x_113 = lean_nat_dec_lt(x_108, x_109);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_97);
lean_ctor_set(x_114, 1, x_98);
lean_ctor_set(x_8, 1, x_114);
lean_ctor_set(x_8, 0, x_112);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_7);
x_116 = lean_apply_2(x_1, lean_box(0), x_115);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_free_object(x_7);
lean_free_object(x_8);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 x_117 = x_13;
} else {
 lean_dec_ref(x_13);
 x_117 = lean_box(0);
}
x_118 = lean_nat_add(x_108, x_110);
lean_inc_ref(x_107);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 3, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_107);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_119, 2, x_109);
if (x_3 == 0)
{
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_array_fget(x_99, x_100);
lean_dec(x_100);
lean_dec_ref(x_99);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc_ref(x_119);
lean_inc_ref(x_112);
lean_inc(x_97);
lean_inc(x_98);
x_128 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9), 8, 7);
lean_closure_set(x_128, 0, x_98);
lean_closure_set(x_128, 1, x_97);
lean_closure_set(x_128, 2, x_112);
lean_closure_set(x_128, 3, x_119);
lean_closure_set(x_128, 4, x_1);
lean_closure_set(x_128, 5, x_2);
lean_closure_set(x_128, 6, x_4);
x_129 = lean_array_fget(x_107, x_108);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_inc(x_2);
lean_inc(x_4);
lean_inc_ref(x_5);
x_130 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed), 11, 10);
lean_closure_set(x_130, 0, x_129);
lean_closure_set(x_130, 1, x_5);
lean_closure_set(x_130, 2, x_4);
lean_closure_set(x_130, 3, x_2);
lean_closure_set(x_130, 4, x_128);
lean_closure_set(x_130, 5, x_97);
lean_closure_set(x_130, 6, x_98);
lean_closure_set(x_130, 7, x_112);
lean_closure_set(x_130, 8, x_119);
lean_closure_set(x_130, 9, x_1);
x_131 = lean_alloc_closure((void*)(l_Lean_Meta_isProof), 6, 1);
lean_closure_set(x_131, 0, x_5);
x_132 = lean_apply_2(x_4, lean_box(0), x_131);
x_133 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_132, x_130);
return x_133;
}
else
{
lean_dec(x_127);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_126;
}
}
block_126:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_box(0);
x_121 = lean_array_push(x_97, x_120);
lean_inc(x_1);
x_122 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed), 6, 5);
lean_closure_set(x_122, 0, x_121);
lean_closure_set(x_122, 1, x_98);
lean_closure_set(x_122, 2, x_112);
lean_closure_set(x_122, 3, x_119);
lean_closure_set(x_122, 4, x_1);
x_123 = lean_box(0);
x_124 = lean_apply_2(x_1, lean_box(0), x_123);
x_125 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_124, x_122);
return x_125;
}
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_134 = lean_ctor_get(x_8, 1);
x_135 = lean_ctor_get(x_8, 0);
x_136 = lean_ctor_get(x_7, 0);
lean_inc(x_136);
lean_dec(x_7);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_139 = x_134;
} else {
 lean_dec_ref(x_134);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_135, 0);
lean_inc_ref(x_140);
x_141 = lean_ctor_get(x_135, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_135, 2);
lean_inc(x_142);
x_143 = lean_nat_dec_lt(x_141, x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_142);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_139)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_139;
}
lean_ctor_set(x_144, 0, x_137);
lean_ctor_set(x_144, 1, x_138);
lean_ctor_set(x_8, 1, x_144);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_136);
lean_ctor_set(x_145, 1, x_8);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = lean_apply_2(x_1, lean_box(0), x_146);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 x_148 = x_135;
} else {
 lean_dec_ref(x_135);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_136, 0);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_136, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_136, 2);
lean_inc(x_151);
x_152 = lean_unsigned_to_nat(1u);
x_153 = lean_nat_add(x_141, x_152);
lean_inc_ref(x_140);
if (lean_is_scalar(x_148)) {
 x_154 = lean_alloc_ctor(0, 3, 0);
} else {
 x_154 = x_148;
}
lean_ctor_set(x_154, 0, x_140);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set(x_154, 2, x_142);
x_155 = lean_nat_dec_lt(x_150, x_151);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_151);
lean_dec(x_150);
lean_dec_ref(x_149);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_139)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_139;
}
lean_ctor_set(x_156, 0, x_137);
lean_ctor_set(x_156, 1, x_138);
lean_ctor_set(x_8, 1, x_156);
lean_ctor_set(x_8, 0, x_154);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_136);
lean_ctor_set(x_157, 1, x_8);
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = lean_apply_2(x_1, lean_box(0), x_158);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_139);
lean_free_object(x_8);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 lean_ctor_release(x_136, 2);
 x_160 = x_136;
} else {
 lean_dec_ref(x_136);
 x_160 = lean_box(0);
}
x_161 = lean_nat_add(x_150, x_152);
lean_inc_ref(x_149);
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(0, 3, 0);
} else {
 x_162 = x_160;
}
lean_ctor_set(x_162, 0, x_149);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set(x_162, 2, x_151);
if (x_3 == 0)
{
lean_dec(x_150);
lean_dec_ref(x_149);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_169;
}
else
{
lean_object* x_170; 
x_170 = lean_array_fget(x_140, x_141);
lean_dec(x_141);
lean_dec_ref(x_140);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc_ref(x_162);
lean_inc_ref(x_154);
lean_inc(x_137);
lean_inc(x_138);
x_171 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9), 8, 7);
lean_closure_set(x_171, 0, x_138);
lean_closure_set(x_171, 1, x_137);
lean_closure_set(x_171, 2, x_154);
lean_closure_set(x_171, 3, x_162);
lean_closure_set(x_171, 4, x_1);
lean_closure_set(x_171, 5, x_2);
lean_closure_set(x_171, 6, x_4);
x_172 = lean_array_fget(x_149, x_150);
lean_dec(x_150);
lean_dec_ref(x_149);
lean_inc(x_2);
lean_inc(x_4);
lean_inc_ref(x_5);
x_173 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed), 11, 10);
lean_closure_set(x_173, 0, x_172);
lean_closure_set(x_173, 1, x_5);
lean_closure_set(x_173, 2, x_4);
lean_closure_set(x_173, 3, x_2);
lean_closure_set(x_173, 4, x_171);
lean_closure_set(x_173, 5, x_137);
lean_closure_set(x_173, 6, x_138);
lean_closure_set(x_173, 7, x_154);
lean_closure_set(x_173, 8, x_162);
lean_closure_set(x_173, 9, x_1);
x_174 = lean_alloc_closure((void*)(l_Lean_Meta_isProof), 6, 1);
lean_closure_set(x_174, 0, x_5);
x_175 = lean_apply_2(x_4, lean_box(0), x_174);
x_176 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_175, x_173);
return x_176;
}
else
{
lean_dec(x_170);
lean_dec(x_150);
lean_dec_ref(x_149);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_169;
}
}
block_169:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_163 = lean_box(0);
x_164 = lean_array_push(x_137, x_163);
lean_inc(x_1);
x_165 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed), 6, 5);
lean_closure_set(x_165, 0, x_164);
lean_closure_set(x_165, 1, x_138);
lean_closure_set(x_165, 2, x_154);
lean_closure_set(x_165, 3, x_162);
lean_closure_set(x_165, 4, x_1);
x_166 = lean_box(0);
x_167 = lean_apply_2(x_1, lean_box(0), x_166);
x_168 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_167, x_165);
return x_168;
}
}
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_177 = lean_ctor_get(x_8, 1);
x_178 = lean_ctor_get(x_8, 0);
lean_inc(x_177);
lean_inc(x_178);
lean_dec(x_8);
x_179 = lean_ctor_get(x_7, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_180 = x_7;
} else {
 lean_dec_ref(x_7);
 x_180 = lean_box(0);
}
x_181 = lean_ctor_get(x_177, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_177, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_183 = x_177;
} else {
 lean_dec_ref(x_177);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_178, 0);
lean_inc_ref(x_184);
x_185 = lean_ctor_get(x_178, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_178, 2);
lean_inc(x_186);
x_187 = lean_nat_dec_lt(x_185, x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec_ref(x_184);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_183)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_183;
}
lean_ctor_set(x_188, 0, x_181);
lean_ctor_set(x_188, 1, x_182);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_178);
lean_ctor_set(x_189, 1, x_188);
if (lean_is_scalar(x_180)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_180;
}
lean_ctor_set(x_190, 0, x_179);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_192 = lean_apply_2(x_1, lean_box(0), x_191);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 lean_ctor_release(x_178, 2);
 x_193 = x_178;
} else {
 lean_dec_ref(x_178);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_179, 0);
lean_inc_ref(x_194);
x_195 = lean_ctor_get(x_179, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_179, 2);
lean_inc(x_196);
x_197 = lean_unsigned_to_nat(1u);
x_198 = lean_nat_add(x_185, x_197);
lean_inc_ref(x_184);
if (lean_is_scalar(x_193)) {
 x_199 = lean_alloc_ctor(0, 3, 0);
} else {
 x_199 = x_193;
}
lean_ctor_set(x_199, 0, x_184);
lean_ctor_set(x_199, 1, x_198);
lean_ctor_set(x_199, 2, x_186);
x_200 = lean_nat_dec_lt(x_195, x_196);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_196);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_185);
lean_dec_ref(x_184);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_183)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_183;
}
lean_ctor_set(x_201, 0, x_181);
lean_ctor_set(x_201, 1, x_182);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_201);
if (lean_is_scalar(x_180)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_180;
}
lean_ctor_set(x_203, 0, x_179);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_204, 0, x_203);
x_205 = lean_apply_2(x_1, lean_box(0), x_204);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_183);
lean_dec(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 lean_ctor_release(x_179, 2);
 x_206 = x_179;
} else {
 lean_dec_ref(x_179);
 x_206 = lean_box(0);
}
x_207 = lean_nat_add(x_195, x_197);
lean_inc_ref(x_194);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 3, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_194);
lean_ctor_set(x_208, 1, x_207);
lean_ctor_set(x_208, 2, x_196);
if (x_3 == 0)
{
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_185);
lean_dec_ref(x_184);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_215;
}
else
{
lean_object* x_216; 
x_216 = lean_array_fget(x_184, x_185);
lean_dec(x_185);
lean_dec_ref(x_184);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc_ref(x_208);
lean_inc_ref(x_199);
lean_inc(x_181);
lean_inc(x_182);
x_217 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9), 8, 7);
lean_closure_set(x_217, 0, x_182);
lean_closure_set(x_217, 1, x_181);
lean_closure_set(x_217, 2, x_199);
lean_closure_set(x_217, 3, x_208);
lean_closure_set(x_217, 4, x_1);
lean_closure_set(x_217, 5, x_2);
lean_closure_set(x_217, 6, x_4);
x_218 = lean_array_fget(x_194, x_195);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_inc(x_2);
lean_inc(x_4);
lean_inc_ref(x_5);
x_219 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed), 11, 10);
lean_closure_set(x_219, 0, x_218);
lean_closure_set(x_219, 1, x_5);
lean_closure_set(x_219, 2, x_4);
lean_closure_set(x_219, 3, x_2);
lean_closure_set(x_219, 4, x_217);
lean_closure_set(x_219, 5, x_181);
lean_closure_set(x_219, 6, x_182);
lean_closure_set(x_219, 7, x_199);
lean_closure_set(x_219, 8, x_208);
lean_closure_set(x_219, 9, x_1);
x_220 = lean_alloc_closure((void*)(l_Lean_Meta_isProof), 6, 1);
lean_closure_set(x_220, 0, x_5);
x_221 = lean_apply_2(x_4, lean_box(0), x_220);
x_222 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_221, x_219);
return x_222;
}
else
{
lean_dec(x_216);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec_ref(x_5);
lean_dec(x_4);
goto block_215;
}
}
block_215:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_209 = lean_box(0);
x_210 = lean_array_push(x_181, x_209);
lean_inc(x_1);
x_211 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed), 6, 5);
lean_closure_set(x_211, 0, x_210);
lean_closure_set(x_211, 1, x_182);
lean_closure_set(x_211, 2, x_199);
lean_closure_set(x_211, 3, x_208);
lean_closure_set(x_211, 4, x_1);
x_212 = lean_box(0);
x_213 = lean_apply_2(x_1, lean_box(0), x_212);
x_214 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_213, x_211);
return x_214;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_push(x_1, x_7);
x_9 = lean_nat_add(x_2, x_3);
lean_inc(x_5);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__13___boxed), 5, 4);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_5);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_5, lean_box(0), x_11);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkEqRefl(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkHEqRefl(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 2);
lean_inc(x_15);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_6);
x_18 = lean_apply_2(x_1, lean_box(0), x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_free_object(x_8);
lean_free_object(x_6);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_10, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_10, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_10, 0);
lean_dec(x_22);
x_23 = lean_array_fget(x_13, x_14);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_14, x_24);
lean_dec(x_14);
lean_ctor_set(x_10, 1, x_25);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed), 5, 4);
lean_closure_set(x_26, 0, x_11);
lean_closure_set(x_26, 1, x_12);
lean_closure_set(x_26, 2, x_10);
lean_closure_set(x_26, 3, x_1);
x_27 = lean_box(0);
x_28 = lean_apply_2(x_1, lean_box(0), x_27);
x_29 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_28, x_26);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
lean_inc(x_2);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14___boxed), 7, 6);
lean_closure_set(x_31, 0, x_12);
lean_closure_set(x_31, 1, x_11);
lean_closure_set(x_31, 2, x_24);
lean_closure_set(x_31, 3, x_10);
lean_closure_set(x_31, 4, x_1);
lean_closure_set(x_31, 5, x_2);
x_32 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__15___boxed), 7, 2);
lean_closure_set(x_32, 0, x_30);
lean_closure_set(x_32, 1, x_4);
x_33 = lean_apply_2(x_3, lean_box(0), x_32);
x_34 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_33, x_31);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_10);
x_35 = lean_array_fget(x_13, x_14);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_14, x_36);
lean_dec(x_14);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_13);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_39 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed), 5, 4);
lean_closure_set(x_39, 0, x_11);
lean_closure_set(x_39, 1, x_12);
lean_closure_set(x_39, 2, x_38);
lean_closure_set(x_39, 3, x_1);
x_40 = lean_box(0);
x_41 = lean_apply_2(x_1, lean_box(0), x_40);
x_42 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_41, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
lean_inc(x_2);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14___boxed), 7, 6);
lean_closure_set(x_44, 0, x_12);
lean_closure_set(x_44, 1, x_11);
lean_closure_set(x_44, 2, x_36);
lean_closure_set(x_44, 3, x_38);
lean_closure_set(x_44, 4, x_1);
lean_closure_set(x_44, 5, x_2);
x_45 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__15___boxed), 7, 2);
lean_closure_set(x_45, 0, x_43);
lean_closure_set(x_45, 1, x_4);
x_46 = lean_apply_2(x_3, lean_box(0), x_45);
x_47 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_46, x_44);
return x_47;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_48 = lean_ctor_get(x_6, 0);
x_49 = lean_ctor_get(x_8, 0);
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_8);
x_51 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_48, 2);
lean_inc(x_53);
x_54 = lean_nat_dec_lt(x_52, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_50);
lean_ctor_set(x_6, 1, x_55);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_6);
x_57 = lean_apply_2(x_1, lean_box(0), x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_free_object(x_6);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 x_58 = x_48;
} else {
 lean_dec_ref(x_48);
 x_58 = lean_box(0);
}
x_59 = lean_array_fget(x_51, x_52);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_52, x_60);
lean_dec(x_52);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 3, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_51);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_53);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_63 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed), 5, 4);
lean_closure_set(x_63, 0, x_49);
lean_closure_set(x_63, 1, x_50);
lean_closure_set(x_63, 2, x_62);
lean_closure_set(x_63, 3, x_1);
x_64 = lean_box(0);
x_65 = lean_apply_2(x_1, lean_box(0), x_64);
x_66 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_65, x_63);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_59, 0);
lean_inc(x_67);
lean_dec(x_59);
lean_inc(x_2);
x_68 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14___boxed), 7, 6);
lean_closure_set(x_68, 0, x_50);
lean_closure_set(x_68, 1, x_49);
lean_closure_set(x_68, 2, x_60);
lean_closure_set(x_68, 3, x_62);
lean_closure_set(x_68, 4, x_1);
lean_closure_set(x_68, 5, x_2);
x_69 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__15___boxed), 7, 2);
lean_closure_set(x_69, 0, x_67);
lean_closure_set(x_69, 1, x_4);
x_70 = lean_apply_2(x_3, lean_box(0), x_69);
x_71 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_70, x_68);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_72 = lean_ctor_get(x_6, 1);
x_73 = lean_ctor_get(x_6, 0);
lean_inc(x_72);
lean_inc(x_73);
lean_dec(x_6);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_73, 2);
lean_inc(x_79);
x_80 = lean_nat_dec_lt(x_78, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_76)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_76;
}
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_75);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_apply_2(x_1, lean_box(0), x_83);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_76);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_85 = x_73;
} else {
 lean_dec_ref(x_73);
 x_85 = lean_box(0);
}
x_86 = lean_array_fget(x_77, x_78);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_add(x_78, x_87);
lean_dec(x_78);
if (lean_is_scalar(x_85)) {
 x_89 = lean_alloc_ctor(0, 3, 0);
} else {
 x_89 = x_85;
}
lean_ctor_set(x_89, 0, x_77);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 2, x_79);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_90 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed), 5, 4);
lean_closure_set(x_90, 0, x_74);
lean_closure_set(x_90, 1, x_75);
lean_closure_set(x_90, 2, x_89);
lean_closure_set(x_90, 3, x_1);
x_91 = lean_box(0);
x_92 = lean_apply_2(x_1, lean_box(0), x_91);
x_93 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_92, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
lean_dec(x_86);
lean_inc(x_2);
x_95 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14___boxed), 7, 6);
lean_closure_set(x_95, 0, x_75);
lean_closure_set(x_95, 1, x_74);
lean_closure_set(x_95, 2, x_87);
lean_closure_set(x_95, 3, x_89);
lean_closure_set(x_95, 4, x_1);
lean_closure_set(x_95, 5, x_2);
x_96 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__15___boxed), 7, 2);
lean_closure_set(x_96, 0, x_94);
lean_closure_set(x_96, 1, x_4);
x_97 = lean_apply_2(x_3, lean_box(0), x_96);
x_98 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_97, x_95);
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_apply_2(x_3, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__17), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_getLevel), 6, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__18), 6, 5);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_9);
lean_closure_set(x_10, 3, x_2);
lean_closure_set(x_10, 4, x_3);
x_11 = 0;
x_12 = 1;
x_13 = 1;
x_14 = lean_box(x_11);
x_15 = lean_box(x_12);
x_16 = lean_box(x_11);
x_17 = lean_box(x_12);
x_18 = lean_box(x_13);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(x_19, 0, x_4);
lean_closure_set(x_19, 1, x_9);
lean_closure_set(x_19, 2, x_14);
lean_closure_set(x_19, 3, x_15);
lean_closure_set(x_19, 4, x_16);
lean_closure_set(x_19, 5, x_17);
lean_closure_set(x_19, 6, x_18);
x_20 = lean_apply_2(x_2, lean_box(0), x_19);
x_21 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_20, x_10);
return x_21;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__20___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Meta_MatcherApp_transform___redArg___lam__20___closed__0;
x_11 = lean_array_get_size(x_1);
x_12 = l_Array_toSubarray___redArg(x_1, x_9, x_11);
x_13 = lean_array_get_size(x_2);
x_14 = l_Array_toSubarray___redArg(x_2, x_9, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_8);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_size(x_3);
x_19 = 0;
x_20 = l_Array_forIn_x27Unsafe_loop___redArg(x_4, x_3, x_5, x_18, x_19, x_17);
x_21 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_20, x_7);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_2(x_1, x_2, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_11);
lean_inc(x_3);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__19), 5, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_11);
lean_inc(x_3);
lean_inc_ref(x_6);
lean_inc_ref(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__20), 8, 7);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_5);
lean_closure_set(x_14, 2, x_11);
lean_closure_set(x_14, 3, x_6);
lean_closure_set(x_14, 4, x_7);
lean_closure_set(x_14, 5, x_3);
lean_closure_set(x_14, 6, x_13);
lean_inc(x_3);
lean_inc_ref(x_11);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed), 6, 5);
lean_closure_set(x_15, 0, x_8);
lean_closure_set(x_15, 1, x_11);
lean_closure_set(x_15, 2, x_12);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_14);
x_16 = lean_array_get_size(x_11);
lean_dec_ref(x_11);
x_17 = lean_array_get_size(x_9);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__22), 2, 1);
lean_closure_set(x_19, 0, x_15);
x_20 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4;
x_21 = l_Nat_reprFast(x_17);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_MessageData_ofFormat(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___redArg(x_6, x_10, x_26);
x_28 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_27, x_19);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_17);
lean_dec_ref(x_10);
lean_dec_ref(x_6);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__22), 2, 1);
lean_closure_set(x_29, 0, x_15);
x_30 = lean_box(0);
x_31 = lean_apply_2(x_1, lean_box(0), x_30);
x_32 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_31, x_29);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_add(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__1;
x_2 = l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__5;
x_2 = l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__4;
x_3 = l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__3;
x_4 = l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__2;
x_5 = l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__6;
x_2 = l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = l_Array_append___redArg(x_1, x_13);
x_15 = l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__9;
x_16 = lean_array_size(x_2);
x_17 = 0;
x_18 = l_Array_mapMUnsafe_map___redArg(x_15, x_3, x_16, x_17, x_2);
x_19 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_5);
lean_ctor_set(x_19, 2, x_6);
lean_ctor_set(x_19, 3, x_7);
lean_ctor_set(x_19, 4, x_8);
lean_ctor_set(x_19, 5, x_9);
lean_ctor_set(x_19, 6, x_10);
lean_ctor_set(x_19, 7, x_18);
lean_ctor_set(x_19, 8, x_11);
lean_ctor_set(x_19, 9, x_14);
x_20 = lean_apply_2(x_12, lean_box(0), x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__25___boxed), 13, 12);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_4);
lean_closure_set(x_19, 4, x_5);
lean_closure_set(x_19, 5, x_6);
lean_closure_set(x_19, 6, x_7);
lean_closure_set(x_19, 7, x_8);
lean_closure_set(x_19, 8, x_9);
lean_closure_set(x_19, 9, x_10);
lean_closure_set(x_19, 10, x_18);
lean_closure_set(x_19, 11, x_11);
x_20 = lean_apply_1(x_12, x_13);
x_21 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_20, x_19);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l_Array_append___redArg(x_1, x_2);
x_8 = 1;
x_9 = lean_box(x_3);
x_10 = lean_box(x_4);
x_11 = lean_box(x_3);
x_12 = lean_box(x_4);
x_13 = lean_box(x_8);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(x_14, 0, x_7);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_9);
lean_closure_set(x_14, 3, x_10);
lean_closure_set(x_14, 4, x_11);
lean_closure_set(x_14, 5, x_12);
lean_closure_set(x_14, 6, x_13);
x_15 = lean_apply_2(x_5, lean_box(0), x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_3(x_1, x_2, x_3, x_6);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_apply_2(x_3, lean_box(0), x_9);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_5);
x_12 = l_Lean_Meta_MatcherApp_withUserNames___redArg(x_6, x_7, x_2, x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_box(x_2);
x_15 = lean_box(x_3);
lean_inc(x_4);
lean_inc_ref(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed), 6, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_12);
lean_closure_set(x_16, 2, x_14);
lean_closure_set(x_16, 3, x_15);
lean_closure_set(x_16, 4, x_4);
lean_inc(x_7);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__28), 6, 5);
lean_closure_set(x_17, 0, x_5);
lean_closure_set(x_17, 1, x_6);
lean_closure_set(x_17, 2, x_13);
lean_closure_set(x_17, 3, x_7);
lean_closure_set(x_17, 4, x_16);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_7);
lean_inc_ref(x_8);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__29), 8, 7);
lean_closure_set(x_18, 0, x_8);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_7);
lean_closure_set(x_18, 4, x_17);
lean_closure_set(x_18, 5, x_9);
lean_closure_set(x_18, 6, x_10);
x_19 = l_Lean_Meta_lambdaTelescope___redArg(x_9, x_10, x_8, x_11, x_2);
x_20 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_19, x_18);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_box(x_1);
x_15 = lean_box(x_2);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__30___boxed), 13, 11);
lean_closure_set(x_16, 0, x_12);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_15);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_4);
lean_closure_set(x_16, 5, x_5);
lean_closure_set(x_16, 6, x_6);
lean_closure_set(x_16, 7, x_7);
lean_closure_set(x_16, 8, x_8);
lean_closure_set(x_16, 9, x_9);
lean_closure_set(x_16, 10, x_10);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_11);
x_18 = l_Lean_Meta_forallBoundedTelescope___redArg(x_8, x_9, x_13, x_17, x_16, x_1, x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_apply_2(x_5, lean_box(0), x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_push(x_1, x_8);
lean_inc(x_5);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32___boxed), 6, 5);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_5);
x_11 = lean_apply_2(x_5, lean_box(0), x_6);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_19, 1);
x_30 = lean_ctor_get(x_19, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_20, 2);
lean_inc(x_33);
x_34 = lean_nat_dec_lt(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_17);
x_36 = lean_apply_2(x_2, lean_box(0), x_35);
x_37 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_36);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_39 = lean_ctor_get(x_20, 2);
lean_dec(x_39);
x_40 = lean_ctor_get(x_20, 1);
lean_dec(x_40);
x_41 = lean_ctor_get(x_20, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_26, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_26, 2);
lean_inc(x_44);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_32, x_45);
lean_inc_ref(x_31);
lean_ctor_set(x_20, 1, x_46);
x_47 = lean_nat_dec_lt(x_43, x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_17);
x_49 = lean_apply_2(x_2, lean_box(0), x_48);
x_50 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_49);
return x_50;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_26);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_52 = lean_ctor_get(x_26, 2);
lean_dec(x_52);
x_53 = lean_ctor_get(x_26, 1);
lean_dec(x_53);
x_54 = lean_ctor_get(x_26, 0);
lean_dec(x_54);
x_55 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_23, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_23, 2);
lean_inc(x_57);
x_58 = lean_nat_add(x_43, x_45);
lean_inc_ref(x_42);
lean_ctor_set(x_26, 1, x_58);
x_59 = lean_nat_dec_lt(x_56, x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_17);
x_61 = lean_apply_2(x_2, lean_box(0), x_60);
x_62 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_61);
return x_62;
}
else
{
uint8_t x_63; 
lean_free_object(x_19);
lean_free_object(x_18);
lean_free_object(x_17);
x_63 = !lean_is_exclusive(x_23);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_64 = lean_ctor_get(x_23, 2);
lean_dec(x_64);
x_65 = lean_ctor_get(x_23, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_23, 0);
lean_dec(x_66);
x_67 = lean_array_fget(x_31, x_32);
lean_dec(x_32);
lean_dec_ref(x_31);
x_68 = lean_array_fget(x_42, x_43);
lean_dec(x_43);
lean_dec_ref(x_42);
x_69 = lean_array_fget(x_55, x_56);
x_70 = lean_box(x_4);
x_71 = lean_box(x_5);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
x_72 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 13, 11);
lean_closure_set(x_72, 0, x_70);
lean_closure_set(x_72, 1, x_71);
lean_closure_set(x_72, 2, x_6);
lean_closure_set(x_72, 3, x_7);
lean_closure_set(x_72, 4, x_14);
lean_closure_set(x_72, 5, x_8);
lean_closure_set(x_72, 6, x_69);
lean_closure_set(x_72, 7, x_9);
lean_closure_set(x_72, 8, x_10);
lean_closure_set(x_72, 9, x_11);
lean_closure_set(x_72, 10, x_12);
x_73 = lean_nat_add(x_56, x_45);
lean_dec(x_56);
lean_ctor_set(x_23, 1, x_73);
lean_inc(x_8);
x_74 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33), 8, 7);
lean_closure_set(x_74, 0, x_29);
lean_closure_set(x_74, 1, x_20);
lean_closure_set(x_74, 2, x_26);
lean_closure_set(x_74, 3, x_23);
lean_closure_set(x_74, 4, x_2);
lean_closure_set(x_74, 5, x_13);
lean_closure_set(x_74, 6, x_8);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_68);
x_76 = l_Lean_Meta_forallBoundedTelescope___redArg(x_9, x_10, x_67, x_75, x_72, x_4, x_4);
x_77 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_76, x_74);
x_78 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_77);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_23);
x_79 = lean_array_fget(x_31, x_32);
lean_dec(x_32);
lean_dec_ref(x_31);
x_80 = lean_array_fget(x_42, x_43);
lean_dec(x_43);
lean_dec_ref(x_42);
x_81 = lean_array_fget(x_55, x_56);
x_82 = lean_box(x_4);
x_83 = lean_box(x_5);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
x_84 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 13, 11);
lean_closure_set(x_84, 0, x_82);
lean_closure_set(x_84, 1, x_83);
lean_closure_set(x_84, 2, x_6);
lean_closure_set(x_84, 3, x_7);
lean_closure_set(x_84, 4, x_14);
lean_closure_set(x_84, 5, x_8);
lean_closure_set(x_84, 6, x_81);
lean_closure_set(x_84, 7, x_9);
lean_closure_set(x_84, 8, x_10);
lean_closure_set(x_84, 9, x_11);
lean_closure_set(x_84, 10, x_12);
x_85 = lean_nat_add(x_56, x_45);
lean_dec(x_56);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_55);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_57);
lean_inc(x_8);
x_87 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33), 8, 7);
lean_closure_set(x_87, 0, x_29);
lean_closure_set(x_87, 1, x_20);
lean_closure_set(x_87, 2, x_26);
lean_closure_set(x_87, 3, x_86);
lean_closure_set(x_87, 4, x_2);
lean_closure_set(x_87, 5, x_13);
lean_closure_set(x_87, 6, x_8);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_80);
x_89 = l_Lean_Meta_forallBoundedTelescope___redArg(x_9, x_10, x_79, x_88, x_84, x_4, x_4);
x_90 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_89, x_87);
x_91 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_26);
x_92 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_23, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_23, 2);
lean_inc(x_94);
x_95 = lean_nat_add(x_43, x_45);
lean_inc_ref(x_42);
x_96 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_96, 0, x_42);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_44);
x_97 = lean_nat_dec_lt(x_93, x_94);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_18, 0, x_96);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_17);
x_99 = lean_apply_2(x_2, lean_box(0), x_98);
x_100 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_99);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_free_object(x_19);
lean_free_object(x_18);
lean_free_object(x_17);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_101 = x_23;
} else {
 lean_dec_ref(x_23);
 x_101 = lean_box(0);
}
x_102 = lean_array_fget(x_31, x_32);
lean_dec(x_32);
lean_dec_ref(x_31);
x_103 = lean_array_fget(x_42, x_43);
lean_dec(x_43);
lean_dec_ref(x_42);
x_104 = lean_array_fget(x_92, x_93);
x_105 = lean_box(x_4);
x_106 = lean_box(x_5);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
x_107 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 13, 11);
lean_closure_set(x_107, 0, x_105);
lean_closure_set(x_107, 1, x_106);
lean_closure_set(x_107, 2, x_6);
lean_closure_set(x_107, 3, x_7);
lean_closure_set(x_107, 4, x_14);
lean_closure_set(x_107, 5, x_8);
lean_closure_set(x_107, 6, x_104);
lean_closure_set(x_107, 7, x_9);
lean_closure_set(x_107, 8, x_10);
lean_closure_set(x_107, 9, x_11);
lean_closure_set(x_107, 10, x_12);
x_108 = lean_nat_add(x_93, x_45);
lean_dec(x_93);
if (lean_is_scalar(x_101)) {
 x_109 = lean_alloc_ctor(0, 3, 0);
} else {
 x_109 = x_101;
}
lean_ctor_set(x_109, 0, x_92);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_109, 2, x_94);
lean_inc(x_8);
x_110 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33), 8, 7);
lean_closure_set(x_110, 0, x_29);
lean_closure_set(x_110, 1, x_20);
lean_closure_set(x_110, 2, x_96);
lean_closure_set(x_110, 3, x_109);
lean_closure_set(x_110, 4, x_2);
lean_closure_set(x_110, 5, x_13);
lean_closure_set(x_110, 6, x_8);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_103);
x_112 = l_Lean_Meta_forallBoundedTelescope___redArg(x_9, x_10, x_102, x_111, x_107, x_4, x_4);
x_113 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_112, x_110);
x_114 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_113);
return x_114;
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_20);
x_115 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_26, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_26, 2);
lean_inc(x_117);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_32, x_118);
lean_inc_ref(x_31);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_31);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_120, 2, x_33);
x_121 = lean_nat_dec_lt(x_116, x_117);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_19, 0, x_120);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_17);
x_123 = lean_apply_2(x_2, lean_box(0), x_122);
x_124 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_123);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_125 = x_26;
} else {
 lean_dec_ref(x_26);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_23, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_23, 2);
lean_inc(x_128);
x_129 = lean_nat_add(x_116, x_118);
lean_inc_ref(x_115);
if (lean_is_scalar(x_125)) {
 x_130 = lean_alloc_ctor(0, 3, 0);
} else {
 x_130 = x_125;
}
lean_ctor_set(x_130, 0, x_115);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_130, 2, x_117);
x_131 = lean_nat_dec_lt(x_127, x_128);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_116);
lean_dec_ref(x_115);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_19, 0, x_120);
lean_ctor_set(x_18, 0, x_130);
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_17);
x_133 = lean_apply_2(x_2, lean_box(0), x_132);
x_134 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_133);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_free_object(x_19);
lean_free_object(x_18);
lean_free_object(x_17);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_135 = x_23;
} else {
 lean_dec_ref(x_23);
 x_135 = lean_box(0);
}
x_136 = lean_array_fget(x_31, x_32);
lean_dec(x_32);
lean_dec_ref(x_31);
x_137 = lean_array_fget(x_115, x_116);
lean_dec(x_116);
lean_dec_ref(x_115);
x_138 = lean_array_fget(x_126, x_127);
x_139 = lean_box(x_4);
x_140 = lean_box(x_5);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
x_141 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 13, 11);
lean_closure_set(x_141, 0, x_139);
lean_closure_set(x_141, 1, x_140);
lean_closure_set(x_141, 2, x_6);
lean_closure_set(x_141, 3, x_7);
lean_closure_set(x_141, 4, x_14);
lean_closure_set(x_141, 5, x_8);
lean_closure_set(x_141, 6, x_138);
lean_closure_set(x_141, 7, x_9);
lean_closure_set(x_141, 8, x_10);
lean_closure_set(x_141, 9, x_11);
lean_closure_set(x_141, 10, x_12);
x_142 = lean_nat_add(x_127, x_118);
lean_dec(x_127);
if (lean_is_scalar(x_135)) {
 x_143 = lean_alloc_ctor(0, 3, 0);
} else {
 x_143 = x_135;
}
lean_ctor_set(x_143, 0, x_126);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_143, 2, x_128);
lean_inc(x_8);
x_144 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33), 8, 7);
lean_closure_set(x_144, 0, x_29);
lean_closure_set(x_144, 1, x_120);
lean_closure_set(x_144, 2, x_130);
lean_closure_set(x_144, 3, x_143);
lean_closure_set(x_144, 4, x_2);
lean_closure_set(x_144, 5, x_13);
lean_closure_set(x_144, 6, x_8);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_137);
x_146 = l_Lean_Meta_forallBoundedTelescope___redArg(x_9, x_10, x_136, x_145, x_141, x_4, x_4);
x_147 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_146, x_144);
x_148 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_147);
return x_148;
}
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_149 = lean_ctor_get(x_19, 1);
lean_inc(x_149);
lean_dec(x_19);
x_150 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_150);
x_151 = lean_ctor_get(x_20, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_20, 2);
lean_inc(x_152);
x_153 = lean_nat_dec_lt(x_151, x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_152);
lean_dec(x_151);
lean_dec_ref(x_150);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_20);
lean_ctor_set(x_154, 1, x_149);
lean_ctor_set(x_18, 1, x_154);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_17);
x_156 = lean_apply_2(x_2, lean_box(0), x_155);
x_157 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_156);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 x_158 = x_20;
} else {
 lean_dec_ref(x_20);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_159);
x_160 = lean_ctor_get(x_26, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_26, 2);
lean_inc(x_161);
x_162 = lean_unsigned_to_nat(1u);
x_163 = lean_nat_add(x_151, x_162);
lean_inc_ref(x_150);
if (lean_is_scalar(x_158)) {
 x_164 = lean_alloc_ctor(0, 3, 0);
} else {
 x_164 = x_158;
}
lean_ctor_set(x_164, 0, x_150);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_164, 2, x_152);
x_165 = lean_nat_dec_lt(x_160, x_161);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_151);
lean_dec_ref(x_150);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_149);
lean_ctor_set(x_18, 1, x_166);
x_167 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_167, 0, x_17);
x_168 = lean_apply_2(x_2, lean_box(0), x_167);
x_169 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_168);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_170 = x_26;
} else {
 lean_dec_ref(x_26);
 x_170 = lean_box(0);
}
x_171 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_23, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_23, 2);
lean_inc(x_173);
x_174 = lean_nat_add(x_160, x_162);
lean_inc_ref(x_159);
if (lean_is_scalar(x_170)) {
 x_175 = lean_alloc_ctor(0, 3, 0);
} else {
 x_175 = x_170;
}
lean_ctor_set(x_175, 0, x_159);
lean_ctor_set(x_175, 1, x_174);
lean_ctor_set(x_175, 2, x_161);
x_176 = lean_nat_dec_lt(x_172, x_173);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_173);
lean_dec(x_172);
lean_dec_ref(x_171);
lean_dec(x_160);
lean_dec_ref(x_159);
lean_dec(x_151);
lean_dec_ref(x_150);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_164);
lean_ctor_set(x_177, 1, x_149);
lean_ctor_set(x_18, 1, x_177);
lean_ctor_set(x_18, 0, x_175);
x_178 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_178, 0, x_17);
x_179 = lean_apply_2(x_2, lean_box(0), x_178);
x_180 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_179);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_free_object(x_18);
lean_free_object(x_17);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_181 = x_23;
} else {
 lean_dec_ref(x_23);
 x_181 = lean_box(0);
}
x_182 = lean_array_fget(x_150, x_151);
lean_dec(x_151);
lean_dec_ref(x_150);
x_183 = lean_array_fget(x_159, x_160);
lean_dec(x_160);
lean_dec_ref(x_159);
x_184 = lean_array_fget(x_171, x_172);
x_185 = lean_box(x_4);
x_186 = lean_box(x_5);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
x_187 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 13, 11);
lean_closure_set(x_187, 0, x_185);
lean_closure_set(x_187, 1, x_186);
lean_closure_set(x_187, 2, x_6);
lean_closure_set(x_187, 3, x_7);
lean_closure_set(x_187, 4, x_14);
lean_closure_set(x_187, 5, x_8);
lean_closure_set(x_187, 6, x_184);
lean_closure_set(x_187, 7, x_9);
lean_closure_set(x_187, 8, x_10);
lean_closure_set(x_187, 9, x_11);
lean_closure_set(x_187, 10, x_12);
x_188 = lean_nat_add(x_172, x_162);
lean_dec(x_172);
if (lean_is_scalar(x_181)) {
 x_189 = lean_alloc_ctor(0, 3, 0);
} else {
 x_189 = x_181;
}
lean_ctor_set(x_189, 0, x_171);
lean_ctor_set(x_189, 1, x_188);
lean_ctor_set(x_189, 2, x_173);
lean_inc(x_8);
x_190 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33), 8, 7);
lean_closure_set(x_190, 0, x_149);
lean_closure_set(x_190, 1, x_164);
lean_closure_set(x_190, 2, x_175);
lean_closure_set(x_190, 3, x_189);
lean_closure_set(x_190, 4, x_2);
lean_closure_set(x_190, 5, x_13);
lean_closure_set(x_190, 6, x_8);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_183);
x_192 = l_Lean_Meta_forallBoundedTelescope___redArg(x_9, x_10, x_182, x_191, x_187, x_4, x_4);
x_193 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_192, x_190);
x_194 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_193);
return x_194;
}
}
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_195 = lean_ctor_get(x_18, 0);
lean_inc(x_195);
lean_dec(x_18);
x_196 = lean_ctor_get(x_19, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_197 = x_19;
} else {
 lean_dec_ref(x_19);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_198);
x_199 = lean_ctor_get(x_20, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_20, 2);
lean_inc(x_200);
x_201 = lean_nat_dec_lt(x_199, x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_197)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_197;
}
lean_ctor_set(x_202, 0, x_20);
lean_ctor_set(x_202, 1, x_196);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_195);
lean_ctor_set(x_203, 1, x_202);
lean_ctor_set(x_17, 1, x_203);
x_204 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_204, 0, x_17);
x_205 = lean_apply_2(x_2, lean_box(0), x_204);
x_206 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_205);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 x_207 = x_20;
} else {
 lean_dec_ref(x_20);
 x_207 = lean_box(0);
}
x_208 = lean_ctor_get(x_195, 0);
lean_inc_ref(x_208);
x_209 = lean_ctor_get(x_195, 1);
lean_inc(x_209);
x_210 = lean_ctor_get(x_195, 2);
lean_inc(x_210);
x_211 = lean_unsigned_to_nat(1u);
x_212 = lean_nat_add(x_199, x_211);
lean_inc_ref(x_198);
if (lean_is_scalar(x_207)) {
 x_213 = lean_alloc_ctor(0, 3, 0);
} else {
 x_213 = x_207;
}
lean_ctor_set(x_213, 0, x_198);
lean_ctor_set(x_213, 1, x_212);
lean_ctor_set(x_213, 2, x_200);
x_214 = lean_nat_dec_lt(x_209, x_210);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_210);
lean_dec(x_209);
lean_dec_ref(x_208);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_197)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_197;
}
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_196);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_195);
lean_ctor_set(x_216, 1, x_215);
lean_ctor_set(x_17, 1, x_216);
x_217 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_217, 0, x_17);
x_218 = lean_apply_2(x_2, lean_box(0), x_217);
x_219 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_218);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 x_220 = x_195;
} else {
 lean_dec_ref(x_195);
 x_220 = lean_box(0);
}
x_221 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_221);
x_222 = lean_ctor_get(x_23, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_23, 2);
lean_inc(x_223);
x_224 = lean_nat_add(x_209, x_211);
lean_inc_ref(x_208);
if (lean_is_scalar(x_220)) {
 x_225 = lean_alloc_ctor(0, 3, 0);
} else {
 x_225 = x_220;
}
lean_ctor_set(x_225, 0, x_208);
lean_ctor_set(x_225, 1, x_224);
lean_ctor_set(x_225, 2, x_210);
x_226 = lean_nat_dec_lt(x_222, x_223);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_223);
lean_dec(x_222);
lean_dec_ref(x_221);
lean_dec(x_209);
lean_dec_ref(x_208);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_197)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_197;
}
lean_ctor_set(x_227, 0, x_213);
lean_ctor_set(x_227, 1, x_196);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_227);
lean_ctor_set(x_17, 1, x_228);
x_229 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_229, 0, x_17);
x_230 = lean_apply_2(x_2, lean_box(0), x_229);
x_231 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_230);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_197);
lean_free_object(x_17);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_232 = x_23;
} else {
 lean_dec_ref(x_23);
 x_232 = lean_box(0);
}
x_233 = lean_array_fget(x_198, x_199);
lean_dec(x_199);
lean_dec_ref(x_198);
x_234 = lean_array_fget(x_208, x_209);
lean_dec(x_209);
lean_dec_ref(x_208);
x_235 = lean_array_fget(x_221, x_222);
x_236 = lean_box(x_4);
x_237 = lean_box(x_5);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
x_238 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 13, 11);
lean_closure_set(x_238, 0, x_236);
lean_closure_set(x_238, 1, x_237);
lean_closure_set(x_238, 2, x_6);
lean_closure_set(x_238, 3, x_7);
lean_closure_set(x_238, 4, x_14);
lean_closure_set(x_238, 5, x_8);
lean_closure_set(x_238, 6, x_235);
lean_closure_set(x_238, 7, x_9);
lean_closure_set(x_238, 8, x_10);
lean_closure_set(x_238, 9, x_11);
lean_closure_set(x_238, 10, x_12);
x_239 = lean_nat_add(x_222, x_211);
lean_dec(x_222);
if (lean_is_scalar(x_232)) {
 x_240 = lean_alloc_ctor(0, 3, 0);
} else {
 x_240 = x_232;
}
lean_ctor_set(x_240, 0, x_221);
lean_ctor_set(x_240, 1, x_239);
lean_ctor_set(x_240, 2, x_223);
lean_inc(x_8);
x_241 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33), 8, 7);
lean_closure_set(x_241, 0, x_196);
lean_closure_set(x_241, 1, x_213);
lean_closure_set(x_241, 2, x_225);
lean_closure_set(x_241, 3, x_240);
lean_closure_set(x_241, 4, x_2);
lean_closure_set(x_241, 5, x_13);
lean_closure_set(x_241, 6, x_8);
x_242 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_242, 0, x_234);
x_243 = l_Lean_Meta_forallBoundedTelescope___redArg(x_9, x_10, x_233, x_242, x_238, x_4, x_4);
x_244 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_243, x_241);
x_245 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_244);
return x_245;
}
}
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_246 = lean_ctor_get(x_17, 0);
lean_inc(x_246);
lean_dec(x_17);
x_247 = lean_ctor_get(x_18, 0);
lean_inc(x_247);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_248 = x_18;
} else {
 lean_dec_ref(x_18);
 x_248 = lean_box(0);
}
x_249 = lean_ctor_get(x_19, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_250 = x_19;
} else {
 lean_dec_ref(x_19);
 x_250 = lean_box(0);
}
x_251 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_251);
x_252 = lean_ctor_get(x_20, 1);
lean_inc(x_252);
x_253 = lean_ctor_get(x_20, 2);
lean_inc(x_253);
x_254 = lean_nat_dec_lt(x_252, x_253);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_253);
lean_dec(x_252);
lean_dec_ref(x_251);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_250)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_250;
}
lean_ctor_set(x_255, 0, x_20);
lean_ctor_set(x_255, 1, x_249);
if (lean_is_scalar(x_248)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_248;
}
lean_ctor_set(x_256, 0, x_247);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_246);
lean_ctor_set(x_257, 1, x_256);
x_258 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_258, 0, x_257);
x_259 = lean_apply_2(x_2, lean_box(0), x_258);
x_260 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_259);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 x_261 = x_20;
} else {
 lean_dec_ref(x_20);
 x_261 = lean_box(0);
}
x_262 = lean_ctor_get(x_247, 0);
lean_inc_ref(x_262);
x_263 = lean_ctor_get(x_247, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_247, 2);
lean_inc(x_264);
x_265 = lean_unsigned_to_nat(1u);
x_266 = lean_nat_add(x_252, x_265);
lean_inc_ref(x_251);
if (lean_is_scalar(x_261)) {
 x_267 = lean_alloc_ctor(0, 3, 0);
} else {
 x_267 = x_261;
}
lean_ctor_set(x_267, 0, x_251);
lean_ctor_set(x_267, 1, x_266);
lean_ctor_set(x_267, 2, x_253);
x_268 = lean_nat_dec_lt(x_263, x_264);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_264);
lean_dec(x_263);
lean_dec_ref(x_262);
lean_dec(x_252);
lean_dec_ref(x_251);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_250)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_250;
}
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_249);
if (lean_is_scalar(x_248)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_248;
}
lean_ctor_set(x_270, 0, x_247);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_246);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_272, 0, x_271);
x_273 = lean_apply_2(x_2, lean_box(0), x_272);
x_274 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_273);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 lean_ctor_release(x_247, 2);
 x_275 = x_247;
} else {
 lean_dec_ref(x_247);
 x_275 = lean_box(0);
}
x_276 = lean_ctor_get(x_246, 0);
lean_inc_ref(x_276);
x_277 = lean_ctor_get(x_246, 1);
lean_inc(x_277);
x_278 = lean_ctor_get(x_246, 2);
lean_inc(x_278);
x_279 = lean_nat_add(x_263, x_265);
lean_inc_ref(x_262);
if (lean_is_scalar(x_275)) {
 x_280 = lean_alloc_ctor(0, 3, 0);
} else {
 x_280 = x_275;
}
lean_ctor_set(x_280, 0, x_262);
lean_ctor_set(x_280, 1, x_279);
lean_ctor_set(x_280, 2, x_264);
x_281 = lean_nat_dec_lt(x_277, x_278);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_278);
lean_dec(x_277);
lean_dec_ref(x_276);
lean_dec(x_263);
lean_dec_ref(x_262);
lean_dec(x_252);
lean_dec_ref(x_251);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_250)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_250;
}
lean_ctor_set(x_282, 0, x_267);
lean_ctor_set(x_282, 1, x_249);
if (lean_is_scalar(x_248)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_248;
}
lean_ctor_set(x_283, 0, x_280);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_246);
lean_ctor_set(x_284, 1, x_283);
x_285 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_285, 0, x_284);
x_286 = lean_apply_2(x_2, lean_box(0), x_285);
x_287 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_286);
return x_287;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_250);
lean_dec(x_248);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 lean_ctor_release(x_246, 2);
 x_288 = x_246;
} else {
 lean_dec_ref(x_246);
 x_288 = lean_box(0);
}
x_289 = lean_array_fget(x_251, x_252);
lean_dec(x_252);
lean_dec_ref(x_251);
x_290 = lean_array_fget(x_262, x_263);
lean_dec(x_263);
lean_dec_ref(x_262);
x_291 = lean_array_fget(x_276, x_277);
x_292 = lean_box(x_4);
x_293 = lean_box(x_5);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
x_294 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 13, 11);
lean_closure_set(x_294, 0, x_292);
lean_closure_set(x_294, 1, x_293);
lean_closure_set(x_294, 2, x_6);
lean_closure_set(x_294, 3, x_7);
lean_closure_set(x_294, 4, x_14);
lean_closure_set(x_294, 5, x_8);
lean_closure_set(x_294, 6, x_291);
lean_closure_set(x_294, 7, x_9);
lean_closure_set(x_294, 8, x_10);
lean_closure_set(x_294, 9, x_11);
lean_closure_set(x_294, 10, x_12);
x_295 = lean_nat_add(x_277, x_265);
lean_dec(x_277);
if (lean_is_scalar(x_288)) {
 x_296 = lean_alloc_ctor(0, 3, 0);
} else {
 x_296 = x_288;
}
lean_ctor_set(x_296, 0, x_276);
lean_ctor_set(x_296, 1, x_295);
lean_ctor_set(x_296, 2, x_278);
lean_inc(x_8);
x_297 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33), 8, 7);
lean_closure_set(x_297, 0, x_249);
lean_closure_set(x_297, 1, x_267);
lean_closure_set(x_297, 2, x_280);
lean_closure_set(x_297, 3, x_296);
lean_closure_set(x_297, 4, x_2);
lean_closure_set(x_297, 5, x_13);
lean_closure_set(x_297, 6, x_8);
x_298 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_298, 0, x_290);
x_299 = l_Lean_Meta_forallBoundedTelescope___redArg(x_9, x_10, x_289, x_298, x_294, x_4, x_4);
x_300 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_299, x_297);
x_301 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_3, x_300);
return x_301;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decLt___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__0;
x_2 = lean_alloc_closure((void*)(l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_20 = l_Std_PRange_instUpwardEnumerableNat;
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Array_toSubarray___redArg(x_1, x_2, x_3);
x_22 = lean_array_get_size(x_4);
lean_inc(x_2);
x_23 = l_Array_toSubarray___redArg(x_4, x_2, x_22);
x_24 = lean_array_get_size(x_19);
lean_inc(x_2);
x_25 = l_Array_toSubarray___redArg(x_19, x_2, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_nat_dec_lt(x_2, x_3);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_apply_2(x_6, lean_box(0), x_28);
x_31 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_30, x_8);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__1;
x_33 = lean_box(0);
x_34 = lean_box(x_11);
x_35 = lean_box(x_12);
lean_inc_ref(x_16);
lean_inc(x_7);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed), 17, 13);
lean_closure_set(x_36, 0, x_9);
lean_closure_set(x_36, 1, x_6);
lean_closure_set(x_36, 2, x_10);
lean_closure_set(x_36, 3, x_34);
lean_closure_set(x_36, 4, x_35);
lean_closure_set(x_36, 5, x_13);
lean_closure_set(x_36, 6, x_14);
lean_closure_set(x_36, 7, x_7);
lean_closure_set(x_36, 8, x_15);
lean_closure_set(x_36, 9, x_16);
lean_closure_set(x_36, 10, x_17);
lean_closure_set(x_36, 11, x_18);
lean_closure_set(x_36, 12, x_33);
x_37 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___redArg(x_20, x_32, x_16, x_3, x_28, x_36, x_2);
x_38 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_37, x_8);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, uint8_t x_19, uint8_t x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29) {
_start:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_13);
lean_inc(x_10);
lean_inc_ref(x_1);
x_30 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__26), 15, 14);
lean_closure_set(x_30, 0, x_28);
lean_closure_set(x_30, 1, x_1);
lean_closure_set(x_30, 2, x_2);
lean_closure_set(x_30, 3, x_3);
lean_closure_set(x_30, 4, x_4);
lean_closure_set(x_30, 5, x_5);
lean_closure_set(x_30, 6, x_6);
lean_closure_set(x_30, 7, x_7);
lean_closure_set(x_30, 8, x_8);
lean_closure_set(x_30, 9, x_9);
lean_closure_set(x_30, 10, x_10);
lean_closure_set(x_30, 11, x_11);
lean_closure_set(x_30, 12, x_12);
lean_closure_set(x_30, 13, x_13);
x_31 = lean_array_get_size(x_14);
x_32 = lean_box(x_19);
x_33 = lean_box(x_20);
lean_inc(x_21);
lean_inc(x_13);
lean_inc(x_31);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed), 19, 18);
lean_closure_set(x_34, 0, x_14);
lean_closure_set(x_34, 1, x_15);
lean_closure_set(x_34, 2, x_31);
lean_closure_set(x_34, 3, x_1);
lean_closure_set(x_34, 4, x_16);
lean_closure_set(x_34, 5, x_10);
lean_closure_set(x_34, 6, x_13);
lean_closure_set(x_34, 7, x_30);
lean_closure_set(x_34, 8, x_17);
lean_closure_set(x_34, 9, x_18);
lean_closure_set(x_34, 10, x_32);
lean_closure_set(x_34, 11, x_33);
lean_closure_set(x_34, 12, x_21);
lean_closure_set(x_34, 13, x_22);
lean_closure_set(x_34, 14, x_23);
lean_closure_set(x_34, 15, x_24);
lean_closure_set(x_34, 16, x_25);
lean_closure_set(x_34, 17, x_26);
x_35 = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN), 7, 2);
lean_closure_set(x_35, 0, x_31);
lean_closure_set(x_35, 1, x_27);
x_36 = lean_apply_2(x_21, lean_box(0), x_35);
x_37 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_36, x_34);
return x_37;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_check), 6, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to transform matcher, type error when constructing new motive:", 69, 69);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10) {
_start:
{
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__1;
x_12 = l_Lean_indentExpr(x_1);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_logError___redArg(x_2, x_3, x_4, x_5, x_15);
x_17 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_16, x_7);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = lean_box(0);
x_19 = lean_apply_2(x_8, lean_box(0), x_18);
x_20 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_19, x_9);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = l_Array_append___redArg(x_1, x_13);
x_15 = l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__9;
x_16 = lean_array_size(x_2);
x_17 = 0;
x_18 = l_Array_mapMUnsafe_map___redArg(x_15, x_3, x_16, x_17, x_2);
x_19 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_5);
lean_ctor_set(x_19, 2, x_6);
lean_ctor_set(x_19, 3, x_7);
lean_ctor_set(x_19, 4, x_8);
lean_ctor_set(x_19, 5, x_9);
lean_ctor_set(x_19, 6, x_10);
lean_ctor_set(x_19, 7, x_18);
lean_ctor_set(x_19, 8, x_11);
lean_ctor_set(x_19, 9, x_14);
x_20 = lean_apply_2(x_12, lean_box(0), x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed), 13, 12);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_4);
lean_closure_set(x_21, 4, x_5);
lean_closure_set(x_21, 5, x_6);
lean_closure_set(x_21, 6, x_7);
lean_closure_set(x_21, 7, x_8);
lean_closure_set(x_21, 8, x_9);
lean_closure_set(x_21, 9, x_10);
lean_closure_set(x_21, 10, x_20);
lean_closure_set(x_21, 11, x_11);
x_22 = lean_apply_1(x_12, x_13);
x_23 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_22, x_21);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = l_Array_append___redArg(x_1, x_2);
x_10 = l_Array_append___redArg(x_9, x_3);
x_11 = l_Array_append___redArg(x_10, x_4);
x_12 = 1;
x_13 = lean_box(x_5);
x_14 = lean_box(x_6);
x_15 = lean_box(x_5);
x_16 = lean_box(x_6);
x_17 = lean_box(x_12);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(x_18, 0, x_11);
lean_closure_set(x_18, 1, x_8);
lean_closure_set(x_18, 2, x_13);
lean_closure_set(x_18, 3, x_14);
lean_closure_set(x_18, 4, x_15);
lean_closure_set(x_18, 5, x_16);
lean_closure_set(x_18, 6, x_17);
x_19 = lean_apply_2(x_7, lean_box(0), x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_3(x_1, x_2, x_3, x_6);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_box(x_5);
x_19 = lean_box(x_6);
lean_inc(x_7);
lean_inc_ref(x_4);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__42___boxed), 8, 7);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_3);
lean_closure_set(x_20, 2, x_4);
lean_closure_set(x_20, 3, x_14);
lean_closure_set(x_20, 4, x_18);
lean_closure_set(x_20, 5, x_19);
lean_closure_set(x_20, 6, x_7);
lean_inc(x_10);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43), 6, 5);
lean_closure_set(x_21, 0, x_8);
lean_closure_set(x_21, 1, x_9);
lean_closure_set(x_21, 2, x_15);
lean_closure_set(x_21, 3, x_10);
lean_closure_set(x_21, 4, x_20);
x_22 = l_Array_append___redArg(x_11, x_4);
lean_dec_ref(x_4);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(x_23, 0, x_12);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_apply_2(x_7, lean_box(0), x_23);
x_25 = lean_apply_3(x_17, lean_box(0), x_24, x_13);
x_26 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_25, x_21);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_box(x_4);
x_19 = lean_box(x_5);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 15, 13);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_16);
lean_closure_set(x_20, 4, x_18);
lean_closure_set(x_20, 5, x_19);
lean_closure_set(x_20, 6, x_6);
lean_closure_set(x_20, 7, x_7);
lean_closure_set(x_20, 8, x_8);
lean_closure_set(x_20, 9, x_9);
lean_closure_set(x_20, 10, x_10);
lean_closure_set(x_20, 11, x_11);
lean_closure_set(x_20, 12, x_12);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_13);
x_22 = l_Lean_Meta_forallBoundedTelescope___redArg(x_14, x_15, x_17, x_21, x_20, x_4, x_4);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_box(x_3);
x_19 = lean_box(x_4);
lean_inc_ref(x_14);
lean_inc_ref(x_13);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__45___boxed), 17, 15);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_16);
lean_closure_set(x_20, 3, x_18);
lean_closure_set(x_20, 4, x_19);
lean_closure_set(x_20, 5, x_5);
lean_closure_set(x_20, 6, x_6);
lean_closure_set(x_20, 7, x_7);
lean_closure_set(x_20, 8, x_8);
lean_closure_set(x_20, 9, x_9);
lean_closure_set(x_20, 10, x_10);
lean_closure_set(x_20, 11, x_11);
lean_closure_set(x_20, 12, x_12);
lean_closure_set(x_20, 13, x_13);
lean_closure_set(x_20, 14, x_14);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_15);
x_22 = l_Lean_Meta_forallBoundedTelescope___redArg(x_13, x_14, x_17, x_21, x_20, x_3, x_3);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_Meta_forallBoundedTelescope___redArg(x_3, x_4, x_7, x_10, x_5, x_6, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_box(x_2);
x_19 = lean_box(x_3);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc(x_7);
lean_inc(x_4);
lean_inc_ref(x_16);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed), 17, 15);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_16);
lean_closure_set(x_20, 2, x_18);
lean_closure_set(x_20, 3, x_19);
lean_closure_set(x_20, 4, x_4);
lean_closure_set(x_20, 5, x_5);
lean_closure_set(x_20, 6, x_6);
lean_closure_set(x_20, 7, x_7);
lean_closure_set(x_20, 8, x_17);
lean_closure_set(x_20, 9, x_8);
lean_closure_set(x_20, 10, x_9);
lean_closure_set(x_20, 11, x_10);
lean_closure_set(x_20, 12, x_11);
lean_closure_set(x_20, 13, x_12);
lean_closure_set(x_20, 14, x_13);
x_21 = lean_box(x_2);
lean_inc_ref(x_16);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed), 7, 6);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_14);
lean_closure_set(x_22, 2, x_11);
lean_closure_set(x_22, 3, x_12);
lean_closure_set(x_22, 4, x_20);
lean_closure_set(x_22, 5, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(x_23, 0, x_15);
lean_closure_set(x_23, 1, x_16);
x_24 = lean_apply_2(x_4, lean_box(0), x_23);
x_25 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_24, x_22);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_apply_2(x_7, lean_box(0), x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_push(x_1, x_10);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed), 8, 7);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
lean_closure_set(x_12, 5, x_6);
lean_closure_set(x_12, 6, x_7);
x_13 = lean_apply_2(x_7, lean_box(0), x_8);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_13, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec_ref(x_1);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_24, 1);
x_41 = lean_ctor_get(x_24, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_25, 2);
lean_inc(x_44);
x_45 = lean_nat_dec_lt(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_20);
x_47 = lean_apply_2(x_2, lean_box(0), x_46);
x_48 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_47);
return x_48;
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_25);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_50 = lean_ctor_get(x_25, 2);
lean_dec(x_50);
x_51 = lean_ctor_get(x_25, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_25, 0);
lean_dec(x_52);
x_53 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_37, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_37, 2);
lean_inc(x_55);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_43, x_56);
lean_inc_ref(x_42);
lean_ctor_set(x_25, 1, x_57);
x_58 = lean_nat_dec_lt(x_54, x_55);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_20);
x_60 = lean_apply_2(x_2, lean_box(0), x_59);
x_61 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_60);
return x_61;
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_37);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_63 = lean_ctor_get(x_37, 2);
lean_dec(x_63);
x_64 = lean_ctor_get(x_37, 1);
lean_dec(x_64);
x_65 = lean_ctor_get(x_37, 0);
lean_dec(x_65);
x_66 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_34, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_34, 2);
lean_inc(x_68);
x_69 = lean_nat_add(x_54, x_56);
lean_inc_ref(x_53);
lean_ctor_set(x_37, 1, x_69);
x_70 = lean_nat_dec_lt(x_67, x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_20);
x_72 = lean_apply_2(x_2, lean_box(0), x_71);
x_73 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_72);
return x_73;
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_34);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_75 = lean_ctor_get(x_34, 2);
lean_dec(x_75);
x_76 = lean_ctor_get(x_34, 1);
lean_dec(x_76);
x_77 = lean_ctor_get(x_34, 0);
lean_dec(x_77);
x_78 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_31, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_31, 2);
lean_inc(x_80);
x_81 = lean_nat_add(x_67, x_56);
lean_inc_ref(x_66);
lean_ctor_set(x_34, 1, x_81);
x_82 = lean_nat_dec_lt(x_79, x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_20);
x_84 = lean_apply_2(x_2, lean_box(0), x_83);
x_85 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_84);
return x_85;
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_31);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_87 = lean_ctor_get(x_31, 2);
lean_dec(x_87);
x_88 = lean_ctor_get(x_31, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_31, 0);
lean_dec(x_89);
x_90 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_28, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_28, 2);
lean_inc(x_92);
x_93 = lean_nat_add(x_79, x_56);
lean_inc_ref(x_78);
lean_ctor_set(x_31, 1, x_93);
x_94 = lean_nat_dec_lt(x_91, x_92);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_20);
x_96 = lean_apply_2(x_2, lean_box(0), x_95);
x_97 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_96);
return x_97;
}
else
{
uint8_t x_98; 
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_20);
x_98 = !lean_is_exclusive(x_28);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_99 = lean_ctor_get(x_28, 2);
lean_dec(x_99);
x_100 = lean_ctor_get(x_28, 1);
lean_dec(x_100);
x_101 = lean_ctor_get(x_28, 0);
lean_dec(x_101);
x_102 = lean_array_fget(x_42, x_43);
lean_dec(x_43);
lean_dec_ref(x_42);
x_103 = lean_array_fget(x_53, x_54);
lean_dec(x_54);
lean_dec_ref(x_53);
x_104 = lean_array_fget(x_66, x_67);
lean_dec(x_67);
lean_dec_ref(x_66);
x_105 = lean_array_fget(x_78, x_79);
lean_dec(x_79);
lean_dec_ref(x_78);
x_106 = lean_array_fget(x_90, x_91);
x_107 = lean_box(x_5);
x_108 = lean_box(x_6);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_9);
x_109 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 15);
lean_closure_set(x_109, 0, x_4);
lean_closure_set(x_109, 1, x_107);
lean_closure_set(x_109, 2, x_108);
lean_closure_set(x_109, 3, x_7);
lean_closure_set(x_109, 4, x_8);
lean_closure_set(x_109, 5, x_17);
lean_closure_set(x_109, 6, x_9);
lean_closure_set(x_109, 7, x_106);
lean_closure_set(x_109, 8, x_10);
lean_closure_set(x_109, 9, x_11);
lean_closure_set(x_109, 10, x_12);
lean_closure_set(x_109, 11, x_13);
lean_closure_set(x_109, 12, x_14);
lean_closure_set(x_109, 13, x_104);
lean_closure_set(x_109, 14, x_102);
x_110 = lean_nat_add(x_91, x_56);
lean_dec(x_91);
lean_ctor_set(x_28, 1, x_110);
lean_inc(x_9);
x_111 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 10, 9);
lean_closure_set(x_111, 0, x_40);
lean_closure_set(x_111, 1, x_25);
lean_closure_set(x_111, 2, x_37);
lean_closure_set(x_111, 3, x_34);
lean_closure_set(x_111, 4, x_31);
lean_closure_set(x_111, 5, x_28);
lean_closure_set(x_111, 6, x_2);
lean_closure_set(x_111, 7, x_15);
lean_closure_set(x_111, 8, x_9);
x_112 = lean_nat_sub(x_105, x_14);
lean_dec(x_14);
lean_dec(x_105);
x_113 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_13, x_12, x_103, x_112, x_16, x_109);
x_114 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_113, x_111);
x_115 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_114);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_28);
x_116 = lean_array_fget(x_42, x_43);
lean_dec(x_43);
lean_dec_ref(x_42);
x_117 = lean_array_fget(x_53, x_54);
lean_dec(x_54);
lean_dec_ref(x_53);
x_118 = lean_array_fget(x_66, x_67);
lean_dec(x_67);
lean_dec_ref(x_66);
x_119 = lean_array_fget(x_78, x_79);
lean_dec(x_79);
lean_dec_ref(x_78);
x_120 = lean_array_fget(x_90, x_91);
x_121 = lean_box(x_5);
x_122 = lean_box(x_6);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_9);
x_123 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 15);
lean_closure_set(x_123, 0, x_4);
lean_closure_set(x_123, 1, x_121);
lean_closure_set(x_123, 2, x_122);
lean_closure_set(x_123, 3, x_7);
lean_closure_set(x_123, 4, x_8);
lean_closure_set(x_123, 5, x_17);
lean_closure_set(x_123, 6, x_9);
lean_closure_set(x_123, 7, x_120);
lean_closure_set(x_123, 8, x_10);
lean_closure_set(x_123, 9, x_11);
lean_closure_set(x_123, 10, x_12);
lean_closure_set(x_123, 11, x_13);
lean_closure_set(x_123, 12, x_14);
lean_closure_set(x_123, 13, x_118);
lean_closure_set(x_123, 14, x_116);
x_124 = lean_nat_add(x_91, x_56);
lean_dec(x_91);
x_125 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_125, 0, x_90);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set(x_125, 2, x_92);
lean_inc(x_9);
x_126 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 10, 9);
lean_closure_set(x_126, 0, x_40);
lean_closure_set(x_126, 1, x_25);
lean_closure_set(x_126, 2, x_37);
lean_closure_set(x_126, 3, x_34);
lean_closure_set(x_126, 4, x_31);
lean_closure_set(x_126, 5, x_125);
lean_closure_set(x_126, 6, x_2);
lean_closure_set(x_126, 7, x_15);
lean_closure_set(x_126, 8, x_9);
x_127 = lean_nat_sub(x_119, x_14);
lean_dec(x_14);
lean_dec(x_119);
x_128 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_13, x_12, x_117, x_127, x_16, x_123);
x_129 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_128, x_126);
x_130 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_129);
return x_130;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_31);
x_131 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_131);
x_132 = lean_ctor_get(x_28, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_28, 2);
lean_inc(x_133);
x_134 = lean_nat_add(x_79, x_56);
lean_inc_ref(x_78);
x_135 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_135, 0, x_78);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set(x_135, 2, x_80);
x_136 = lean_nat_dec_lt(x_132, x_133);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_ctor_set(x_21, 0, x_135);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_20);
x_138 = lean_apply_2(x_2, lean_box(0), x_137);
x_139 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_138);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_20);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_140 = x_28;
} else {
 lean_dec_ref(x_28);
 x_140 = lean_box(0);
}
x_141 = lean_array_fget(x_42, x_43);
lean_dec(x_43);
lean_dec_ref(x_42);
x_142 = lean_array_fget(x_53, x_54);
lean_dec(x_54);
lean_dec_ref(x_53);
x_143 = lean_array_fget(x_66, x_67);
lean_dec(x_67);
lean_dec_ref(x_66);
x_144 = lean_array_fget(x_78, x_79);
lean_dec(x_79);
lean_dec_ref(x_78);
x_145 = lean_array_fget(x_131, x_132);
x_146 = lean_box(x_5);
x_147 = lean_box(x_6);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_9);
x_148 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 15);
lean_closure_set(x_148, 0, x_4);
lean_closure_set(x_148, 1, x_146);
lean_closure_set(x_148, 2, x_147);
lean_closure_set(x_148, 3, x_7);
lean_closure_set(x_148, 4, x_8);
lean_closure_set(x_148, 5, x_17);
lean_closure_set(x_148, 6, x_9);
lean_closure_set(x_148, 7, x_145);
lean_closure_set(x_148, 8, x_10);
lean_closure_set(x_148, 9, x_11);
lean_closure_set(x_148, 10, x_12);
lean_closure_set(x_148, 11, x_13);
lean_closure_set(x_148, 12, x_14);
lean_closure_set(x_148, 13, x_143);
lean_closure_set(x_148, 14, x_141);
x_149 = lean_nat_add(x_132, x_56);
lean_dec(x_132);
if (lean_is_scalar(x_140)) {
 x_150 = lean_alloc_ctor(0, 3, 0);
} else {
 x_150 = x_140;
}
lean_ctor_set(x_150, 0, x_131);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set(x_150, 2, x_133);
lean_inc(x_9);
x_151 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 10, 9);
lean_closure_set(x_151, 0, x_40);
lean_closure_set(x_151, 1, x_25);
lean_closure_set(x_151, 2, x_37);
lean_closure_set(x_151, 3, x_34);
lean_closure_set(x_151, 4, x_135);
lean_closure_set(x_151, 5, x_150);
lean_closure_set(x_151, 6, x_2);
lean_closure_set(x_151, 7, x_15);
lean_closure_set(x_151, 8, x_9);
x_152 = lean_nat_sub(x_144, x_14);
lean_dec(x_14);
lean_dec(x_144);
x_153 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_13, x_12, x_142, x_152, x_16, x_148);
x_154 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_153, x_151);
x_155 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_154);
return x_155;
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_dec(x_34);
x_156 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_156);
x_157 = lean_ctor_get(x_31, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_31, 2);
lean_inc(x_158);
x_159 = lean_nat_add(x_67, x_56);
lean_inc_ref(x_66);
x_160 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_160, 0, x_66);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set(x_160, 2, x_68);
x_161 = lean_nat_dec_lt(x_157, x_158);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec_ref(x_156);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_ctor_set(x_22, 0, x_160);
x_162 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_162, 0, x_20);
x_163 = lean_apply_2(x_2, lean_box(0), x_162);
x_164 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_163);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_165 = x_31;
} else {
 lean_dec_ref(x_31);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_166);
x_167 = lean_ctor_get(x_28, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_28, 2);
lean_inc(x_168);
x_169 = lean_nat_add(x_157, x_56);
lean_inc_ref(x_156);
if (lean_is_scalar(x_165)) {
 x_170 = lean_alloc_ctor(0, 3, 0);
} else {
 x_170 = x_165;
}
lean_ctor_set(x_170, 0, x_156);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set(x_170, 2, x_158);
x_171 = lean_nat_dec_lt(x_167, x_168);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_168);
lean_dec(x_167);
lean_dec_ref(x_166);
lean_dec(x_157);
lean_dec_ref(x_156);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_ctor_set(x_22, 0, x_160);
lean_ctor_set(x_21, 0, x_170);
x_172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_172, 0, x_20);
x_173 = lean_apply_2(x_2, lean_box(0), x_172);
x_174 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_173);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_20);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_175 = x_28;
} else {
 lean_dec_ref(x_28);
 x_175 = lean_box(0);
}
x_176 = lean_array_fget(x_42, x_43);
lean_dec(x_43);
lean_dec_ref(x_42);
x_177 = lean_array_fget(x_53, x_54);
lean_dec(x_54);
lean_dec_ref(x_53);
x_178 = lean_array_fget(x_66, x_67);
lean_dec(x_67);
lean_dec_ref(x_66);
x_179 = lean_array_fget(x_156, x_157);
lean_dec(x_157);
lean_dec_ref(x_156);
x_180 = lean_array_fget(x_166, x_167);
x_181 = lean_box(x_5);
x_182 = lean_box(x_6);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_9);
x_183 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 15);
lean_closure_set(x_183, 0, x_4);
lean_closure_set(x_183, 1, x_181);
lean_closure_set(x_183, 2, x_182);
lean_closure_set(x_183, 3, x_7);
lean_closure_set(x_183, 4, x_8);
lean_closure_set(x_183, 5, x_17);
lean_closure_set(x_183, 6, x_9);
lean_closure_set(x_183, 7, x_180);
lean_closure_set(x_183, 8, x_10);
lean_closure_set(x_183, 9, x_11);
lean_closure_set(x_183, 10, x_12);
lean_closure_set(x_183, 11, x_13);
lean_closure_set(x_183, 12, x_14);
lean_closure_set(x_183, 13, x_178);
lean_closure_set(x_183, 14, x_176);
x_184 = lean_nat_add(x_167, x_56);
lean_dec(x_167);
if (lean_is_scalar(x_175)) {
 x_185 = lean_alloc_ctor(0, 3, 0);
} else {
 x_185 = x_175;
}
lean_ctor_set(x_185, 0, x_166);
lean_ctor_set(x_185, 1, x_184);
lean_ctor_set(x_185, 2, x_168);
lean_inc(x_9);
x_186 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 10, 9);
lean_closure_set(x_186, 0, x_40);
lean_closure_set(x_186, 1, x_25);
lean_closure_set(x_186, 2, x_37);
lean_closure_set(x_186, 3, x_160);
lean_closure_set(x_186, 4, x_170);
lean_closure_set(x_186, 5, x_185);
lean_closure_set(x_186, 6, x_2);
lean_closure_set(x_186, 7, x_15);
lean_closure_set(x_186, 8, x_9);
x_187 = lean_nat_sub(x_179, x_14);
lean_dec(x_14);
lean_dec(x_179);
x_188 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_13, x_12, x_177, x_187, x_16, x_183);
x_189 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_188, x_186);
x_190 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_189);
return x_190;
}
}
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
lean_dec(x_37);
x_191 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_191);
x_192 = lean_ctor_get(x_34, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_34, 2);
lean_inc(x_193);
x_194 = lean_nat_add(x_54, x_56);
lean_inc_ref(x_53);
x_195 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_195, 0, x_53);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set(x_195, 2, x_55);
x_196 = lean_nat_dec_lt(x_192, x_193);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_193);
lean_dec(x_192);
lean_dec_ref(x_191);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_ctor_set(x_23, 0, x_195);
x_197 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_197, 0, x_20);
x_198 = lean_apply_2(x_2, lean_box(0), x_197);
x_199 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_198);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 x_200 = x_34;
} else {
 lean_dec_ref(x_34);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_201);
x_202 = lean_ctor_get(x_31, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_31, 2);
lean_inc(x_203);
x_204 = lean_nat_add(x_192, x_56);
lean_inc_ref(x_191);
if (lean_is_scalar(x_200)) {
 x_205 = lean_alloc_ctor(0, 3, 0);
} else {
 x_205 = x_200;
}
lean_ctor_set(x_205, 0, x_191);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set(x_205, 2, x_193);
x_206 = lean_nat_dec_lt(x_202, x_203);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_203);
lean_dec(x_202);
lean_dec_ref(x_201);
lean_dec(x_192);
lean_dec_ref(x_191);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_ctor_set(x_23, 0, x_195);
lean_ctor_set(x_22, 0, x_205);
x_207 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_207, 0, x_20);
x_208 = lean_apply_2(x_2, lean_box(0), x_207);
x_209 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_208);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_210 = x_31;
} else {
 lean_dec_ref(x_31);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_211);
x_212 = lean_ctor_get(x_28, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_28, 2);
lean_inc(x_213);
x_214 = lean_nat_add(x_202, x_56);
lean_inc_ref(x_201);
if (lean_is_scalar(x_210)) {
 x_215 = lean_alloc_ctor(0, 3, 0);
} else {
 x_215 = x_210;
}
lean_ctor_set(x_215, 0, x_201);
lean_ctor_set(x_215, 1, x_214);
lean_ctor_set(x_215, 2, x_203);
x_216 = lean_nat_dec_lt(x_212, x_213);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_213);
lean_dec(x_212);
lean_dec_ref(x_211);
lean_dec(x_202);
lean_dec_ref(x_201);
lean_dec(x_192);
lean_dec_ref(x_191);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_ctor_set(x_23, 0, x_195);
lean_ctor_set(x_22, 0, x_205);
lean_ctor_set(x_21, 0, x_215);
x_217 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_217, 0, x_20);
x_218 = lean_apply_2(x_2, lean_box(0), x_217);
x_219 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_218);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_20);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_220 = x_28;
} else {
 lean_dec_ref(x_28);
 x_220 = lean_box(0);
}
x_221 = lean_array_fget(x_42, x_43);
lean_dec(x_43);
lean_dec_ref(x_42);
x_222 = lean_array_fget(x_53, x_54);
lean_dec(x_54);
lean_dec_ref(x_53);
x_223 = lean_array_fget(x_191, x_192);
lean_dec(x_192);
lean_dec_ref(x_191);
x_224 = lean_array_fget(x_201, x_202);
lean_dec(x_202);
lean_dec_ref(x_201);
x_225 = lean_array_fget(x_211, x_212);
x_226 = lean_box(x_5);
x_227 = lean_box(x_6);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_9);
x_228 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 15);
lean_closure_set(x_228, 0, x_4);
lean_closure_set(x_228, 1, x_226);
lean_closure_set(x_228, 2, x_227);
lean_closure_set(x_228, 3, x_7);
lean_closure_set(x_228, 4, x_8);
lean_closure_set(x_228, 5, x_17);
lean_closure_set(x_228, 6, x_9);
lean_closure_set(x_228, 7, x_225);
lean_closure_set(x_228, 8, x_10);
lean_closure_set(x_228, 9, x_11);
lean_closure_set(x_228, 10, x_12);
lean_closure_set(x_228, 11, x_13);
lean_closure_set(x_228, 12, x_14);
lean_closure_set(x_228, 13, x_223);
lean_closure_set(x_228, 14, x_221);
x_229 = lean_nat_add(x_212, x_56);
lean_dec(x_212);
if (lean_is_scalar(x_220)) {
 x_230 = lean_alloc_ctor(0, 3, 0);
} else {
 x_230 = x_220;
}
lean_ctor_set(x_230, 0, x_211);
lean_ctor_set(x_230, 1, x_229);
lean_ctor_set(x_230, 2, x_213);
lean_inc(x_9);
x_231 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 10, 9);
lean_closure_set(x_231, 0, x_40);
lean_closure_set(x_231, 1, x_25);
lean_closure_set(x_231, 2, x_195);
lean_closure_set(x_231, 3, x_205);
lean_closure_set(x_231, 4, x_215);
lean_closure_set(x_231, 5, x_230);
lean_closure_set(x_231, 6, x_2);
lean_closure_set(x_231, 7, x_15);
lean_closure_set(x_231, 8, x_9);
x_232 = lean_nat_sub(x_224, x_14);
lean_dec(x_14);
lean_dec(x_224);
x_233 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_13, x_12, x_222, x_232, x_16, x_228);
x_234 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_233, x_231);
x_235 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_234);
return x_235;
}
}
}
}
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
lean_dec(x_25);
x_236 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_236);
x_237 = lean_ctor_get(x_37, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_37, 2);
lean_inc(x_238);
x_239 = lean_unsigned_to_nat(1u);
x_240 = lean_nat_add(x_43, x_239);
lean_inc_ref(x_42);
x_241 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_241, 0, x_42);
lean_ctor_set(x_241, 1, x_240);
lean_ctor_set(x_241, 2, x_44);
x_242 = lean_nat_dec_lt(x_237, x_238);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_ctor_set(x_24, 0, x_241);
x_243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_243, 0, x_20);
x_244 = lean_apply_2(x_2, lean_box(0), x_243);
x_245 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_244);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_246 = x_37;
} else {
 lean_dec_ref(x_37);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_247);
x_248 = lean_ctor_get(x_34, 1);
lean_inc(x_248);
x_249 = lean_ctor_get(x_34, 2);
lean_inc(x_249);
x_250 = lean_nat_add(x_237, x_239);
lean_inc_ref(x_236);
if (lean_is_scalar(x_246)) {
 x_251 = lean_alloc_ctor(0, 3, 0);
} else {
 x_251 = x_246;
}
lean_ctor_set(x_251, 0, x_236);
lean_ctor_set(x_251, 1, x_250);
lean_ctor_set(x_251, 2, x_238);
x_252 = lean_nat_dec_lt(x_248, x_249);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_249);
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_ctor_set(x_24, 0, x_241);
lean_ctor_set(x_23, 0, x_251);
x_253 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_253, 0, x_20);
x_254 = lean_apply_2(x_2, lean_box(0), x_253);
x_255 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_254);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 x_256 = x_34;
} else {
 lean_dec_ref(x_34);
 x_256 = lean_box(0);
}
x_257 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_257);
x_258 = lean_ctor_get(x_31, 1);
lean_inc(x_258);
x_259 = lean_ctor_get(x_31, 2);
lean_inc(x_259);
x_260 = lean_nat_add(x_248, x_239);
lean_inc_ref(x_247);
if (lean_is_scalar(x_256)) {
 x_261 = lean_alloc_ctor(0, 3, 0);
} else {
 x_261 = x_256;
}
lean_ctor_set(x_261, 0, x_247);
lean_ctor_set(x_261, 1, x_260);
lean_ctor_set(x_261, 2, x_249);
x_262 = lean_nat_dec_lt(x_258, x_259);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_259);
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_ctor_set(x_24, 0, x_241);
lean_ctor_set(x_23, 0, x_251);
lean_ctor_set(x_22, 0, x_261);
x_263 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_263, 0, x_20);
x_264 = lean_apply_2(x_2, lean_box(0), x_263);
x_265 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_264);
return x_265;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_266 = x_31;
} else {
 lean_dec_ref(x_31);
 x_266 = lean_box(0);
}
x_267 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_267);
x_268 = lean_ctor_get(x_28, 1);
lean_inc(x_268);
x_269 = lean_ctor_get(x_28, 2);
lean_inc(x_269);
x_270 = lean_nat_add(x_258, x_239);
lean_inc_ref(x_257);
if (lean_is_scalar(x_266)) {
 x_271 = lean_alloc_ctor(0, 3, 0);
} else {
 x_271 = x_266;
}
lean_ctor_set(x_271, 0, x_257);
lean_ctor_set(x_271, 1, x_270);
lean_ctor_set(x_271, 2, x_259);
x_272 = lean_nat_dec_lt(x_268, x_269);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_269);
lean_dec(x_268);
lean_dec_ref(x_267);
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_ctor_set(x_24, 0, x_241);
lean_ctor_set(x_23, 0, x_251);
lean_ctor_set(x_22, 0, x_261);
lean_ctor_set(x_21, 0, x_271);
x_273 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_273, 0, x_20);
x_274 = lean_apply_2(x_2, lean_box(0), x_273);
x_275 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_274);
return x_275;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_free_object(x_24);
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_20);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_276 = x_28;
} else {
 lean_dec_ref(x_28);
 x_276 = lean_box(0);
}
x_277 = lean_array_fget(x_42, x_43);
lean_dec(x_43);
lean_dec_ref(x_42);
x_278 = lean_array_fget(x_236, x_237);
lean_dec(x_237);
lean_dec_ref(x_236);
x_279 = lean_array_fget(x_247, x_248);
lean_dec(x_248);
lean_dec_ref(x_247);
x_280 = lean_array_fget(x_257, x_258);
lean_dec(x_258);
lean_dec_ref(x_257);
x_281 = lean_array_fget(x_267, x_268);
x_282 = lean_box(x_5);
x_283 = lean_box(x_6);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_9);
x_284 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 15);
lean_closure_set(x_284, 0, x_4);
lean_closure_set(x_284, 1, x_282);
lean_closure_set(x_284, 2, x_283);
lean_closure_set(x_284, 3, x_7);
lean_closure_set(x_284, 4, x_8);
lean_closure_set(x_284, 5, x_17);
lean_closure_set(x_284, 6, x_9);
lean_closure_set(x_284, 7, x_281);
lean_closure_set(x_284, 8, x_10);
lean_closure_set(x_284, 9, x_11);
lean_closure_set(x_284, 10, x_12);
lean_closure_set(x_284, 11, x_13);
lean_closure_set(x_284, 12, x_14);
lean_closure_set(x_284, 13, x_279);
lean_closure_set(x_284, 14, x_277);
x_285 = lean_nat_add(x_268, x_239);
lean_dec(x_268);
if (lean_is_scalar(x_276)) {
 x_286 = lean_alloc_ctor(0, 3, 0);
} else {
 x_286 = x_276;
}
lean_ctor_set(x_286, 0, x_267);
lean_ctor_set(x_286, 1, x_285);
lean_ctor_set(x_286, 2, x_269);
lean_inc(x_9);
x_287 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 10, 9);
lean_closure_set(x_287, 0, x_40);
lean_closure_set(x_287, 1, x_241);
lean_closure_set(x_287, 2, x_251);
lean_closure_set(x_287, 3, x_261);
lean_closure_set(x_287, 4, x_271);
lean_closure_set(x_287, 5, x_286);
lean_closure_set(x_287, 6, x_2);
lean_closure_set(x_287, 7, x_15);
lean_closure_set(x_287, 8, x_9);
x_288 = lean_nat_sub(x_280, x_14);
lean_dec(x_14);
lean_dec(x_280);
x_289 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_13, x_12, x_278, x_288, x_16, x_284);
x_290 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_289, x_287);
x_291 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_290);
return x_291;
}
}
}
}
}
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_292 = lean_ctor_get(x_24, 1);
lean_inc(x_292);
lean_dec(x_24);
x_293 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_293);
x_294 = lean_ctor_get(x_25, 1);
lean_inc(x_294);
x_295 = lean_ctor_get(x_25, 2);
lean_inc(x_295);
x_296 = lean_nat_dec_lt(x_294, x_295);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_295);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_25);
lean_ctor_set(x_297, 1, x_292);
lean_ctor_set(x_23, 1, x_297);
x_298 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_298, 0, x_20);
x_299 = lean_apply_2(x_2, lean_box(0), x_298);
x_300 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_299);
return x_300;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_301 = x_25;
} else {
 lean_dec_ref(x_25);
 x_301 = lean_box(0);
}
x_302 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_302);
x_303 = lean_ctor_get(x_37, 1);
lean_inc(x_303);
x_304 = lean_ctor_get(x_37, 2);
lean_inc(x_304);
x_305 = lean_unsigned_to_nat(1u);
x_306 = lean_nat_add(x_294, x_305);
lean_inc_ref(x_293);
if (lean_is_scalar(x_301)) {
 x_307 = lean_alloc_ctor(0, 3, 0);
} else {
 x_307 = x_301;
}
lean_ctor_set(x_307, 0, x_293);
lean_ctor_set(x_307, 1, x_306);
lean_ctor_set(x_307, 2, x_295);
x_308 = lean_nat_dec_lt(x_303, x_304);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_304);
lean_dec(x_303);
lean_dec_ref(x_302);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_292);
lean_ctor_set(x_23, 1, x_309);
x_310 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_310, 0, x_20);
x_311 = lean_apply_2(x_2, lean_box(0), x_310);
x_312 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_311);
return x_312;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_313 = x_37;
} else {
 lean_dec_ref(x_37);
 x_313 = lean_box(0);
}
x_314 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_314);
x_315 = lean_ctor_get(x_34, 1);
lean_inc(x_315);
x_316 = lean_ctor_get(x_34, 2);
lean_inc(x_316);
x_317 = lean_nat_add(x_303, x_305);
lean_inc_ref(x_302);
if (lean_is_scalar(x_313)) {
 x_318 = lean_alloc_ctor(0, 3, 0);
} else {
 x_318 = x_313;
}
lean_ctor_set(x_318, 0, x_302);
lean_ctor_set(x_318, 1, x_317);
lean_ctor_set(x_318, 2, x_304);
x_319 = lean_nat_dec_lt(x_315, x_316);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_316);
lean_dec(x_315);
lean_dec_ref(x_314);
lean_dec(x_303);
lean_dec_ref(x_302);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_307);
lean_ctor_set(x_320, 1, x_292);
lean_ctor_set(x_23, 1, x_320);
lean_ctor_set(x_23, 0, x_318);
x_321 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_321, 0, x_20);
x_322 = lean_apply_2(x_2, lean_box(0), x_321);
x_323 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_322);
return x_323;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 x_324 = x_34;
} else {
 lean_dec_ref(x_34);
 x_324 = lean_box(0);
}
x_325 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_325);
x_326 = lean_ctor_get(x_31, 1);
lean_inc(x_326);
x_327 = lean_ctor_get(x_31, 2);
lean_inc(x_327);
x_328 = lean_nat_add(x_315, x_305);
lean_inc_ref(x_314);
if (lean_is_scalar(x_324)) {
 x_329 = lean_alloc_ctor(0, 3, 0);
} else {
 x_329 = x_324;
}
lean_ctor_set(x_329, 0, x_314);
lean_ctor_set(x_329, 1, x_328);
lean_ctor_set(x_329, 2, x_316);
x_330 = lean_nat_dec_lt(x_326, x_327);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_327);
lean_dec(x_326);
lean_dec_ref(x_325);
lean_dec(x_315);
lean_dec_ref(x_314);
lean_dec(x_303);
lean_dec_ref(x_302);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_307);
lean_ctor_set(x_331, 1, x_292);
lean_ctor_set(x_23, 1, x_331);
lean_ctor_set(x_23, 0, x_318);
lean_ctor_set(x_22, 0, x_329);
x_332 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_332, 0, x_20);
x_333 = lean_apply_2(x_2, lean_box(0), x_332);
x_334 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_333);
return x_334;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; 
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_335 = x_31;
} else {
 lean_dec_ref(x_31);
 x_335 = lean_box(0);
}
x_336 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_336);
x_337 = lean_ctor_get(x_28, 1);
lean_inc(x_337);
x_338 = lean_ctor_get(x_28, 2);
lean_inc(x_338);
x_339 = lean_nat_add(x_326, x_305);
lean_inc_ref(x_325);
if (lean_is_scalar(x_335)) {
 x_340 = lean_alloc_ctor(0, 3, 0);
} else {
 x_340 = x_335;
}
lean_ctor_set(x_340, 0, x_325);
lean_ctor_set(x_340, 1, x_339);
lean_ctor_set(x_340, 2, x_327);
x_341 = lean_nat_dec_lt(x_337, x_338);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
lean_dec(x_338);
lean_dec(x_337);
lean_dec_ref(x_336);
lean_dec(x_326);
lean_dec_ref(x_325);
lean_dec(x_315);
lean_dec_ref(x_314);
lean_dec(x_303);
lean_dec_ref(x_302);
lean_dec(x_294);
lean_dec_ref(x_293);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_307);
lean_ctor_set(x_342, 1, x_292);
lean_ctor_set(x_23, 1, x_342);
lean_ctor_set(x_23, 0, x_318);
lean_ctor_set(x_22, 0, x_329);
lean_ctor_set(x_21, 0, x_340);
x_343 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_343, 0, x_20);
x_344 = lean_apply_2(x_2, lean_box(0), x_343);
x_345 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_344);
return x_345;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_free_object(x_23);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_20);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_346 = x_28;
} else {
 lean_dec_ref(x_28);
 x_346 = lean_box(0);
}
x_347 = lean_array_fget(x_293, x_294);
lean_dec(x_294);
lean_dec_ref(x_293);
x_348 = lean_array_fget(x_302, x_303);
lean_dec(x_303);
lean_dec_ref(x_302);
x_349 = lean_array_fget(x_314, x_315);
lean_dec(x_315);
lean_dec_ref(x_314);
x_350 = lean_array_fget(x_325, x_326);
lean_dec(x_326);
lean_dec_ref(x_325);
x_351 = lean_array_fget(x_336, x_337);
x_352 = lean_box(x_5);
x_353 = lean_box(x_6);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_9);
x_354 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 15);
lean_closure_set(x_354, 0, x_4);
lean_closure_set(x_354, 1, x_352);
lean_closure_set(x_354, 2, x_353);
lean_closure_set(x_354, 3, x_7);
lean_closure_set(x_354, 4, x_8);
lean_closure_set(x_354, 5, x_17);
lean_closure_set(x_354, 6, x_9);
lean_closure_set(x_354, 7, x_351);
lean_closure_set(x_354, 8, x_10);
lean_closure_set(x_354, 9, x_11);
lean_closure_set(x_354, 10, x_12);
lean_closure_set(x_354, 11, x_13);
lean_closure_set(x_354, 12, x_14);
lean_closure_set(x_354, 13, x_349);
lean_closure_set(x_354, 14, x_347);
x_355 = lean_nat_add(x_337, x_305);
lean_dec(x_337);
if (lean_is_scalar(x_346)) {
 x_356 = lean_alloc_ctor(0, 3, 0);
} else {
 x_356 = x_346;
}
lean_ctor_set(x_356, 0, x_336);
lean_ctor_set(x_356, 1, x_355);
lean_ctor_set(x_356, 2, x_338);
lean_inc(x_9);
x_357 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 10, 9);
lean_closure_set(x_357, 0, x_292);
lean_closure_set(x_357, 1, x_307);
lean_closure_set(x_357, 2, x_318);
lean_closure_set(x_357, 3, x_329);
lean_closure_set(x_357, 4, x_340);
lean_closure_set(x_357, 5, x_356);
lean_closure_set(x_357, 6, x_2);
lean_closure_set(x_357, 7, x_15);
lean_closure_set(x_357, 8, x_9);
x_358 = lean_nat_sub(x_350, x_14);
lean_dec(x_14);
lean_dec(x_350);
x_359 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_13, x_12, x_348, x_358, x_16, x_354);
x_360 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_359, x_357);
x_361 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_360);
return x_361;
}
}
}
}
}
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_362 = lean_ctor_get(x_23, 0);
lean_inc(x_362);
lean_dec(x_23);
x_363 = lean_ctor_get(x_24, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_364 = x_24;
} else {
 lean_dec_ref(x_24);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_365);
x_366 = lean_ctor_get(x_25, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_25, 2);
lean_inc(x_367);
x_368 = lean_nat_dec_lt(x_366, x_367);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_365);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_364)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_364;
}
lean_ctor_set(x_369, 0, x_25);
lean_ctor_set(x_369, 1, x_363);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_362);
lean_ctor_set(x_370, 1, x_369);
lean_ctor_set(x_22, 1, x_370);
x_371 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_371, 0, x_20);
x_372 = lean_apply_2(x_2, lean_box(0), x_371);
x_373 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_372);
return x_373;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_374 = x_25;
} else {
 lean_dec_ref(x_25);
 x_374 = lean_box(0);
}
x_375 = lean_ctor_get(x_362, 0);
lean_inc_ref(x_375);
x_376 = lean_ctor_get(x_362, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_362, 2);
lean_inc(x_377);
x_378 = lean_unsigned_to_nat(1u);
x_379 = lean_nat_add(x_366, x_378);
lean_inc_ref(x_365);
if (lean_is_scalar(x_374)) {
 x_380 = lean_alloc_ctor(0, 3, 0);
} else {
 x_380 = x_374;
}
lean_ctor_set(x_380, 0, x_365);
lean_ctor_set(x_380, 1, x_379);
lean_ctor_set(x_380, 2, x_367);
x_381 = lean_nat_dec_lt(x_376, x_377);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec(x_377);
lean_dec(x_376);
lean_dec_ref(x_375);
lean_dec(x_366);
lean_dec_ref(x_365);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_364)) {
 x_382 = lean_alloc_ctor(0, 2, 0);
} else {
 x_382 = x_364;
}
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_363);
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_362);
lean_ctor_set(x_383, 1, x_382);
lean_ctor_set(x_22, 1, x_383);
x_384 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_384, 0, x_20);
x_385 = lean_apply_2(x_2, lean_box(0), x_384);
x_386 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_385);
return x_386;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; 
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 lean_ctor_release(x_362, 2);
 x_387 = x_362;
} else {
 lean_dec_ref(x_362);
 x_387 = lean_box(0);
}
x_388 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_388);
x_389 = lean_ctor_get(x_34, 1);
lean_inc(x_389);
x_390 = lean_ctor_get(x_34, 2);
lean_inc(x_390);
x_391 = lean_nat_add(x_376, x_378);
lean_inc_ref(x_375);
if (lean_is_scalar(x_387)) {
 x_392 = lean_alloc_ctor(0, 3, 0);
} else {
 x_392 = x_387;
}
lean_ctor_set(x_392, 0, x_375);
lean_ctor_set(x_392, 1, x_391);
lean_ctor_set(x_392, 2, x_377);
x_393 = lean_nat_dec_lt(x_389, x_390);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_390);
lean_dec(x_389);
lean_dec_ref(x_388);
lean_dec(x_376);
lean_dec_ref(x_375);
lean_dec(x_366);
lean_dec_ref(x_365);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_364)) {
 x_394 = lean_alloc_ctor(0, 2, 0);
} else {
 x_394 = x_364;
}
lean_ctor_set(x_394, 0, x_380);
lean_ctor_set(x_394, 1, x_363);
x_395 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_395, 0, x_392);
lean_ctor_set(x_395, 1, x_394);
lean_ctor_set(x_22, 1, x_395);
x_396 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_396, 0, x_20);
x_397 = lean_apply_2(x_2, lean_box(0), x_396);
x_398 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_397);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; 
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 x_399 = x_34;
} else {
 lean_dec_ref(x_34);
 x_399 = lean_box(0);
}
x_400 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_400);
x_401 = lean_ctor_get(x_31, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_31, 2);
lean_inc(x_402);
x_403 = lean_nat_add(x_389, x_378);
lean_inc_ref(x_388);
if (lean_is_scalar(x_399)) {
 x_404 = lean_alloc_ctor(0, 3, 0);
} else {
 x_404 = x_399;
}
lean_ctor_set(x_404, 0, x_388);
lean_ctor_set(x_404, 1, x_403);
lean_ctor_set(x_404, 2, x_390);
x_405 = lean_nat_dec_lt(x_401, x_402);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_402);
lean_dec(x_401);
lean_dec_ref(x_400);
lean_dec(x_389);
lean_dec_ref(x_388);
lean_dec(x_376);
lean_dec_ref(x_375);
lean_dec(x_366);
lean_dec_ref(x_365);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_364)) {
 x_406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_406 = x_364;
}
lean_ctor_set(x_406, 0, x_380);
lean_ctor_set(x_406, 1, x_363);
x_407 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_407, 0, x_392);
lean_ctor_set(x_407, 1, x_406);
lean_ctor_set(x_22, 1, x_407);
lean_ctor_set(x_22, 0, x_404);
x_408 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_408, 0, x_20);
x_409 = lean_apply_2(x_2, lean_box(0), x_408);
x_410 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_409);
return x_410;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; 
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_411 = x_31;
} else {
 lean_dec_ref(x_31);
 x_411 = lean_box(0);
}
x_412 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_412);
x_413 = lean_ctor_get(x_28, 1);
lean_inc(x_413);
x_414 = lean_ctor_get(x_28, 2);
lean_inc(x_414);
x_415 = lean_nat_add(x_401, x_378);
lean_inc_ref(x_400);
if (lean_is_scalar(x_411)) {
 x_416 = lean_alloc_ctor(0, 3, 0);
} else {
 x_416 = x_411;
}
lean_ctor_set(x_416, 0, x_400);
lean_ctor_set(x_416, 1, x_415);
lean_ctor_set(x_416, 2, x_402);
x_417 = lean_nat_dec_lt(x_413, x_414);
if (x_417 == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_414);
lean_dec(x_413);
lean_dec_ref(x_412);
lean_dec(x_401);
lean_dec_ref(x_400);
lean_dec(x_389);
lean_dec_ref(x_388);
lean_dec(x_376);
lean_dec_ref(x_375);
lean_dec(x_366);
lean_dec_ref(x_365);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_364)) {
 x_418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_418 = x_364;
}
lean_ctor_set(x_418, 0, x_380);
lean_ctor_set(x_418, 1, x_363);
x_419 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_419, 0, x_392);
lean_ctor_set(x_419, 1, x_418);
lean_ctor_set(x_22, 1, x_419);
lean_ctor_set(x_22, 0, x_404);
lean_ctor_set(x_21, 0, x_416);
x_420 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_420, 0, x_20);
x_421 = lean_apply_2(x_2, lean_box(0), x_420);
x_422 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_421);
return x_422;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_dec(x_364);
lean_free_object(x_22);
lean_free_object(x_21);
lean_free_object(x_20);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_423 = x_28;
} else {
 lean_dec_ref(x_28);
 x_423 = lean_box(0);
}
x_424 = lean_array_fget(x_365, x_366);
lean_dec(x_366);
lean_dec_ref(x_365);
x_425 = lean_array_fget(x_375, x_376);
lean_dec(x_376);
lean_dec_ref(x_375);
x_426 = lean_array_fget(x_388, x_389);
lean_dec(x_389);
lean_dec_ref(x_388);
x_427 = lean_array_fget(x_400, x_401);
lean_dec(x_401);
lean_dec_ref(x_400);
x_428 = lean_array_fget(x_412, x_413);
x_429 = lean_box(x_5);
x_430 = lean_box(x_6);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_9);
x_431 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 15);
lean_closure_set(x_431, 0, x_4);
lean_closure_set(x_431, 1, x_429);
lean_closure_set(x_431, 2, x_430);
lean_closure_set(x_431, 3, x_7);
lean_closure_set(x_431, 4, x_8);
lean_closure_set(x_431, 5, x_17);
lean_closure_set(x_431, 6, x_9);
lean_closure_set(x_431, 7, x_428);
lean_closure_set(x_431, 8, x_10);
lean_closure_set(x_431, 9, x_11);
lean_closure_set(x_431, 10, x_12);
lean_closure_set(x_431, 11, x_13);
lean_closure_set(x_431, 12, x_14);
lean_closure_set(x_431, 13, x_426);
lean_closure_set(x_431, 14, x_424);
x_432 = lean_nat_add(x_413, x_378);
lean_dec(x_413);
if (lean_is_scalar(x_423)) {
 x_433 = lean_alloc_ctor(0, 3, 0);
} else {
 x_433 = x_423;
}
lean_ctor_set(x_433, 0, x_412);
lean_ctor_set(x_433, 1, x_432);
lean_ctor_set(x_433, 2, x_414);
lean_inc(x_9);
x_434 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 10, 9);
lean_closure_set(x_434, 0, x_363);
lean_closure_set(x_434, 1, x_380);
lean_closure_set(x_434, 2, x_392);
lean_closure_set(x_434, 3, x_404);
lean_closure_set(x_434, 4, x_416);
lean_closure_set(x_434, 5, x_433);
lean_closure_set(x_434, 6, x_2);
lean_closure_set(x_434, 7, x_15);
lean_closure_set(x_434, 8, x_9);
x_435 = lean_nat_sub(x_427, x_14);
lean_dec(x_14);
lean_dec(x_427);
x_436 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_13, x_12, x_425, x_435, x_16, x_431);
x_437 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_436, x_434);
x_438 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_437);
return x_438;
}
}
}
}
}
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; 
x_439 = lean_ctor_get(x_22, 0);
lean_inc(x_439);
lean_dec(x_22);
x_440 = lean_ctor_get(x_23, 0);
lean_inc(x_440);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_441 = x_23;
} else {
 lean_dec_ref(x_23);
 x_441 = lean_box(0);
}
x_442 = lean_ctor_get(x_24, 1);
lean_inc(x_442);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_443 = x_24;
} else {
 lean_dec_ref(x_24);
 x_443 = lean_box(0);
}
x_444 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_444);
x_445 = lean_ctor_get(x_25, 1);
lean_inc(x_445);
x_446 = lean_ctor_get(x_25, 2);
lean_inc(x_446);
x_447 = lean_nat_dec_lt(x_445, x_446);
if (x_447 == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_446);
lean_dec(x_445);
lean_dec_ref(x_444);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_443)) {
 x_448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_448 = x_443;
}
lean_ctor_set(x_448, 0, x_25);
lean_ctor_set(x_448, 1, x_442);
if (lean_is_scalar(x_441)) {
 x_449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_449 = x_441;
}
lean_ctor_set(x_449, 0, x_440);
lean_ctor_set(x_449, 1, x_448);
x_450 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_450, 0, x_439);
lean_ctor_set(x_450, 1, x_449);
lean_ctor_set(x_21, 1, x_450);
x_451 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_451, 0, x_20);
x_452 = lean_apply_2(x_2, lean_box(0), x_451);
x_453 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_452);
return x_453;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_454 = x_25;
} else {
 lean_dec_ref(x_25);
 x_454 = lean_box(0);
}
x_455 = lean_ctor_get(x_440, 0);
lean_inc_ref(x_455);
x_456 = lean_ctor_get(x_440, 1);
lean_inc(x_456);
x_457 = lean_ctor_get(x_440, 2);
lean_inc(x_457);
x_458 = lean_unsigned_to_nat(1u);
x_459 = lean_nat_add(x_445, x_458);
lean_inc_ref(x_444);
if (lean_is_scalar(x_454)) {
 x_460 = lean_alloc_ctor(0, 3, 0);
} else {
 x_460 = x_454;
}
lean_ctor_set(x_460, 0, x_444);
lean_ctor_set(x_460, 1, x_459);
lean_ctor_set(x_460, 2, x_446);
x_461 = lean_nat_dec_lt(x_456, x_457);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
lean_dec(x_457);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_445);
lean_dec_ref(x_444);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_443)) {
 x_462 = lean_alloc_ctor(0, 2, 0);
} else {
 x_462 = x_443;
}
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_442);
if (lean_is_scalar(x_441)) {
 x_463 = lean_alloc_ctor(0, 2, 0);
} else {
 x_463 = x_441;
}
lean_ctor_set(x_463, 0, x_440);
lean_ctor_set(x_463, 1, x_462);
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_439);
lean_ctor_set(x_464, 1, x_463);
lean_ctor_set(x_21, 1, x_464);
x_465 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_465, 0, x_20);
x_466 = lean_apply_2(x_2, lean_box(0), x_465);
x_467 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_466);
return x_467;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; uint8_t x_474; 
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 lean_ctor_release(x_440, 2);
 x_468 = x_440;
} else {
 lean_dec_ref(x_440);
 x_468 = lean_box(0);
}
x_469 = lean_ctor_get(x_439, 0);
lean_inc_ref(x_469);
x_470 = lean_ctor_get(x_439, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_439, 2);
lean_inc(x_471);
x_472 = lean_nat_add(x_456, x_458);
lean_inc_ref(x_455);
if (lean_is_scalar(x_468)) {
 x_473 = lean_alloc_ctor(0, 3, 0);
} else {
 x_473 = x_468;
}
lean_ctor_set(x_473, 0, x_455);
lean_ctor_set(x_473, 1, x_472);
lean_ctor_set(x_473, 2, x_457);
x_474 = lean_nat_dec_lt(x_470, x_471);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
lean_dec(x_471);
lean_dec(x_470);
lean_dec_ref(x_469);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_445);
lean_dec_ref(x_444);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_443)) {
 x_475 = lean_alloc_ctor(0, 2, 0);
} else {
 x_475 = x_443;
}
lean_ctor_set(x_475, 0, x_460);
lean_ctor_set(x_475, 1, x_442);
if (lean_is_scalar(x_441)) {
 x_476 = lean_alloc_ctor(0, 2, 0);
} else {
 x_476 = x_441;
}
lean_ctor_set(x_476, 0, x_473);
lean_ctor_set(x_476, 1, x_475);
x_477 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_477, 0, x_439);
lean_ctor_set(x_477, 1, x_476);
lean_ctor_set(x_21, 1, x_477);
x_478 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_478, 0, x_20);
x_479 = lean_apply_2(x_2, lean_box(0), x_478);
x_480 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_479);
return x_480;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; 
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 lean_ctor_release(x_439, 2);
 x_481 = x_439;
} else {
 lean_dec_ref(x_439);
 x_481 = lean_box(0);
}
x_482 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_482);
x_483 = lean_ctor_get(x_31, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_31, 2);
lean_inc(x_484);
x_485 = lean_nat_add(x_470, x_458);
lean_inc_ref(x_469);
if (lean_is_scalar(x_481)) {
 x_486 = lean_alloc_ctor(0, 3, 0);
} else {
 x_486 = x_481;
}
lean_ctor_set(x_486, 0, x_469);
lean_ctor_set(x_486, 1, x_485);
lean_ctor_set(x_486, 2, x_471);
x_487 = lean_nat_dec_lt(x_483, x_484);
if (x_487 == 0)
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
lean_dec(x_484);
lean_dec(x_483);
lean_dec_ref(x_482);
lean_dec(x_470);
lean_dec_ref(x_469);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_445);
lean_dec_ref(x_444);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_443)) {
 x_488 = lean_alloc_ctor(0, 2, 0);
} else {
 x_488 = x_443;
}
lean_ctor_set(x_488, 0, x_460);
lean_ctor_set(x_488, 1, x_442);
if (lean_is_scalar(x_441)) {
 x_489 = lean_alloc_ctor(0, 2, 0);
} else {
 x_489 = x_441;
}
lean_ctor_set(x_489, 0, x_473);
lean_ctor_set(x_489, 1, x_488);
x_490 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_490, 0, x_486);
lean_ctor_set(x_490, 1, x_489);
lean_ctor_set(x_21, 1, x_490);
x_491 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_491, 0, x_20);
x_492 = lean_apply_2(x_2, lean_box(0), x_491);
x_493 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_492);
return x_493;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; 
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_494 = x_31;
} else {
 lean_dec_ref(x_31);
 x_494 = lean_box(0);
}
x_495 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_495);
x_496 = lean_ctor_get(x_28, 1);
lean_inc(x_496);
x_497 = lean_ctor_get(x_28, 2);
lean_inc(x_497);
x_498 = lean_nat_add(x_483, x_458);
lean_inc_ref(x_482);
if (lean_is_scalar(x_494)) {
 x_499 = lean_alloc_ctor(0, 3, 0);
} else {
 x_499 = x_494;
}
lean_ctor_set(x_499, 0, x_482);
lean_ctor_set(x_499, 1, x_498);
lean_ctor_set(x_499, 2, x_484);
x_500 = lean_nat_dec_lt(x_496, x_497);
if (x_500 == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
lean_dec(x_497);
lean_dec(x_496);
lean_dec_ref(x_495);
lean_dec(x_483);
lean_dec_ref(x_482);
lean_dec(x_470);
lean_dec_ref(x_469);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_445);
lean_dec_ref(x_444);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_443)) {
 x_501 = lean_alloc_ctor(0, 2, 0);
} else {
 x_501 = x_443;
}
lean_ctor_set(x_501, 0, x_460);
lean_ctor_set(x_501, 1, x_442);
if (lean_is_scalar(x_441)) {
 x_502 = lean_alloc_ctor(0, 2, 0);
} else {
 x_502 = x_441;
}
lean_ctor_set(x_502, 0, x_473);
lean_ctor_set(x_502, 1, x_501);
x_503 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_503, 0, x_486);
lean_ctor_set(x_503, 1, x_502);
lean_ctor_set(x_21, 1, x_503);
lean_ctor_set(x_21, 0, x_499);
x_504 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_504, 0, x_20);
x_505 = lean_apply_2(x_2, lean_box(0), x_504);
x_506 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_505);
return x_506;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_dec(x_443);
lean_dec(x_441);
lean_free_object(x_21);
lean_free_object(x_20);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_507 = x_28;
} else {
 lean_dec_ref(x_28);
 x_507 = lean_box(0);
}
x_508 = lean_array_fget(x_444, x_445);
lean_dec(x_445);
lean_dec_ref(x_444);
x_509 = lean_array_fget(x_455, x_456);
lean_dec(x_456);
lean_dec_ref(x_455);
x_510 = lean_array_fget(x_469, x_470);
lean_dec(x_470);
lean_dec_ref(x_469);
x_511 = lean_array_fget(x_482, x_483);
lean_dec(x_483);
lean_dec_ref(x_482);
x_512 = lean_array_fget(x_495, x_496);
x_513 = lean_box(x_5);
x_514 = lean_box(x_6);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_9);
x_515 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 15);
lean_closure_set(x_515, 0, x_4);
lean_closure_set(x_515, 1, x_513);
lean_closure_set(x_515, 2, x_514);
lean_closure_set(x_515, 3, x_7);
lean_closure_set(x_515, 4, x_8);
lean_closure_set(x_515, 5, x_17);
lean_closure_set(x_515, 6, x_9);
lean_closure_set(x_515, 7, x_512);
lean_closure_set(x_515, 8, x_10);
lean_closure_set(x_515, 9, x_11);
lean_closure_set(x_515, 10, x_12);
lean_closure_set(x_515, 11, x_13);
lean_closure_set(x_515, 12, x_14);
lean_closure_set(x_515, 13, x_510);
lean_closure_set(x_515, 14, x_508);
x_516 = lean_nat_add(x_496, x_458);
lean_dec(x_496);
if (lean_is_scalar(x_507)) {
 x_517 = lean_alloc_ctor(0, 3, 0);
} else {
 x_517 = x_507;
}
lean_ctor_set(x_517, 0, x_495);
lean_ctor_set(x_517, 1, x_516);
lean_ctor_set(x_517, 2, x_497);
lean_inc(x_9);
x_518 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 10, 9);
lean_closure_set(x_518, 0, x_442);
lean_closure_set(x_518, 1, x_460);
lean_closure_set(x_518, 2, x_473);
lean_closure_set(x_518, 3, x_486);
lean_closure_set(x_518, 4, x_499);
lean_closure_set(x_518, 5, x_517);
lean_closure_set(x_518, 6, x_2);
lean_closure_set(x_518, 7, x_15);
lean_closure_set(x_518, 8, x_9);
x_519 = lean_nat_sub(x_511, x_14);
lean_dec(x_14);
lean_dec(x_511);
x_520 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_13, x_12, x_509, x_519, x_16, x_515);
x_521 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_520, x_518);
x_522 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_521);
return x_522;
}
}
}
}
}
}
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; uint8_t x_533; 
x_523 = lean_ctor_get(x_21, 0);
lean_inc(x_523);
lean_dec(x_21);
x_524 = lean_ctor_get(x_22, 0);
lean_inc(x_524);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_525 = x_22;
} else {
 lean_dec_ref(x_22);
 x_525 = lean_box(0);
}
x_526 = lean_ctor_get(x_23, 0);
lean_inc(x_526);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_527 = x_23;
} else {
 lean_dec_ref(x_23);
 x_527 = lean_box(0);
}
x_528 = lean_ctor_get(x_24, 1);
lean_inc(x_528);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_529 = x_24;
} else {
 lean_dec_ref(x_24);
 x_529 = lean_box(0);
}
x_530 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_530);
x_531 = lean_ctor_get(x_25, 1);
lean_inc(x_531);
x_532 = lean_ctor_get(x_25, 2);
lean_inc(x_532);
x_533 = lean_nat_dec_lt(x_531, x_532);
if (x_533 == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_532);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_529)) {
 x_534 = lean_alloc_ctor(0, 2, 0);
} else {
 x_534 = x_529;
}
lean_ctor_set(x_534, 0, x_25);
lean_ctor_set(x_534, 1, x_528);
if (lean_is_scalar(x_527)) {
 x_535 = lean_alloc_ctor(0, 2, 0);
} else {
 x_535 = x_527;
}
lean_ctor_set(x_535, 0, x_526);
lean_ctor_set(x_535, 1, x_534);
if (lean_is_scalar(x_525)) {
 x_536 = lean_alloc_ctor(0, 2, 0);
} else {
 x_536 = x_525;
}
lean_ctor_set(x_536, 0, x_524);
lean_ctor_set(x_536, 1, x_535);
x_537 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_537, 0, x_523);
lean_ctor_set(x_537, 1, x_536);
lean_ctor_set(x_20, 1, x_537);
x_538 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_538, 0, x_20);
x_539 = lean_apply_2(x_2, lean_box(0), x_538);
x_540 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_539);
return x_540;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; uint8_t x_548; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_541 = x_25;
} else {
 lean_dec_ref(x_25);
 x_541 = lean_box(0);
}
x_542 = lean_ctor_get(x_526, 0);
lean_inc_ref(x_542);
x_543 = lean_ctor_get(x_526, 1);
lean_inc(x_543);
x_544 = lean_ctor_get(x_526, 2);
lean_inc(x_544);
x_545 = lean_unsigned_to_nat(1u);
x_546 = lean_nat_add(x_531, x_545);
lean_inc_ref(x_530);
if (lean_is_scalar(x_541)) {
 x_547 = lean_alloc_ctor(0, 3, 0);
} else {
 x_547 = x_541;
}
lean_ctor_set(x_547, 0, x_530);
lean_ctor_set(x_547, 1, x_546);
lean_ctor_set(x_547, 2, x_532);
x_548 = lean_nat_dec_lt(x_543, x_544);
if (x_548 == 0)
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
lean_dec(x_544);
lean_dec(x_543);
lean_dec_ref(x_542);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_529)) {
 x_549 = lean_alloc_ctor(0, 2, 0);
} else {
 x_549 = x_529;
}
lean_ctor_set(x_549, 0, x_547);
lean_ctor_set(x_549, 1, x_528);
if (lean_is_scalar(x_527)) {
 x_550 = lean_alloc_ctor(0, 2, 0);
} else {
 x_550 = x_527;
}
lean_ctor_set(x_550, 0, x_526);
lean_ctor_set(x_550, 1, x_549);
if (lean_is_scalar(x_525)) {
 x_551 = lean_alloc_ctor(0, 2, 0);
} else {
 x_551 = x_525;
}
lean_ctor_set(x_551, 0, x_524);
lean_ctor_set(x_551, 1, x_550);
x_552 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_552, 0, x_523);
lean_ctor_set(x_552, 1, x_551);
lean_ctor_set(x_20, 1, x_552);
x_553 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_553, 0, x_20);
x_554 = lean_apply_2(x_2, lean_box(0), x_553);
x_555 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_554);
return x_555;
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; uint8_t x_562; 
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 lean_ctor_release(x_526, 2);
 x_556 = x_526;
} else {
 lean_dec_ref(x_526);
 x_556 = lean_box(0);
}
x_557 = lean_ctor_get(x_524, 0);
lean_inc_ref(x_557);
x_558 = lean_ctor_get(x_524, 1);
lean_inc(x_558);
x_559 = lean_ctor_get(x_524, 2);
lean_inc(x_559);
x_560 = lean_nat_add(x_543, x_545);
lean_inc_ref(x_542);
if (lean_is_scalar(x_556)) {
 x_561 = lean_alloc_ctor(0, 3, 0);
} else {
 x_561 = x_556;
}
lean_ctor_set(x_561, 0, x_542);
lean_ctor_set(x_561, 1, x_560);
lean_ctor_set(x_561, 2, x_544);
x_562 = lean_nat_dec_lt(x_558, x_559);
if (x_562 == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_559);
lean_dec(x_558);
lean_dec_ref(x_557);
lean_dec(x_543);
lean_dec_ref(x_542);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_529)) {
 x_563 = lean_alloc_ctor(0, 2, 0);
} else {
 x_563 = x_529;
}
lean_ctor_set(x_563, 0, x_547);
lean_ctor_set(x_563, 1, x_528);
if (lean_is_scalar(x_527)) {
 x_564 = lean_alloc_ctor(0, 2, 0);
} else {
 x_564 = x_527;
}
lean_ctor_set(x_564, 0, x_561);
lean_ctor_set(x_564, 1, x_563);
if (lean_is_scalar(x_525)) {
 x_565 = lean_alloc_ctor(0, 2, 0);
} else {
 x_565 = x_525;
}
lean_ctor_set(x_565, 0, x_524);
lean_ctor_set(x_565, 1, x_564);
x_566 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_566, 0, x_523);
lean_ctor_set(x_566, 1, x_565);
lean_ctor_set(x_20, 1, x_566);
x_567 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_567, 0, x_20);
x_568 = lean_apply_2(x_2, lean_box(0), x_567);
x_569 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_568);
return x_569;
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; 
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 lean_ctor_release(x_524, 2);
 x_570 = x_524;
} else {
 lean_dec_ref(x_524);
 x_570 = lean_box(0);
}
x_571 = lean_ctor_get(x_523, 0);
lean_inc_ref(x_571);
x_572 = lean_ctor_get(x_523, 1);
lean_inc(x_572);
x_573 = lean_ctor_get(x_523, 2);
lean_inc(x_573);
x_574 = lean_nat_add(x_558, x_545);
lean_inc_ref(x_557);
if (lean_is_scalar(x_570)) {
 x_575 = lean_alloc_ctor(0, 3, 0);
} else {
 x_575 = x_570;
}
lean_ctor_set(x_575, 0, x_557);
lean_ctor_set(x_575, 1, x_574);
lean_ctor_set(x_575, 2, x_559);
x_576 = lean_nat_dec_lt(x_572, x_573);
if (x_576 == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
lean_dec(x_573);
lean_dec(x_572);
lean_dec_ref(x_571);
lean_dec(x_558);
lean_dec_ref(x_557);
lean_dec(x_543);
lean_dec_ref(x_542);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_529)) {
 x_577 = lean_alloc_ctor(0, 2, 0);
} else {
 x_577 = x_529;
}
lean_ctor_set(x_577, 0, x_547);
lean_ctor_set(x_577, 1, x_528);
if (lean_is_scalar(x_527)) {
 x_578 = lean_alloc_ctor(0, 2, 0);
} else {
 x_578 = x_527;
}
lean_ctor_set(x_578, 0, x_561);
lean_ctor_set(x_578, 1, x_577);
if (lean_is_scalar(x_525)) {
 x_579 = lean_alloc_ctor(0, 2, 0);
} else {
 x_579 = x_525;
}
lean_ctor_set(x_579, 0, x_575);
lean_ctor_set(x_579, 1, x_578);
x_580 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_580, 0, x_523);
lean_ctor_set(x_580, 1, x_579);
lean_ctor_set(x_20, 1, x_580);
x_581 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_581, 0, x_20);
x_582 = lean_apply_2(x_2, lean_box(0), x_581);
x_583 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_582);
return x_583;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; uint8_t x_590; 
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 lean_ctor_release(x_523, 1);
 lean_ctor_release(x_523, 2);
 x_584 = x_523;
} else {
 lean_dec_ref(x_523);
 x_584 = lean_box(0);
}
x_585 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_585);
x_586 = lean_ctor_get(x_28, 1);
lean_inc(x_586);
x_587 = lean_ctor_get(x_28, 2);
lean_inc(x_587);
x_588 = lean_nat_add(x_572, x_545);
lean_inc_ref(x_571);
if (lean_is_scalar(x_584)) {
 x_589 = lean_alloc_ctor(0, 3, 0);
} else {
 x_589 = x_584;
}
lean_ctor_set(x_589, 0, x_571);
lean_ctor_set(x_589, 1, x_588);
lean_ctor_set(x_589, 2, x_573);
x_590 = lean_nat_dec_lt(x_586, x_587);
if (x_590 == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
lean_dec(x_587);
lean_dec(x_586);
lean_dec_ref(x_585);
lean_dec(x_572);
lean_dec_ref(x_571);
lean_dec(x_558);
lean_dec_ref(x_557);
lean_dec(x_543);
lean_dec_ref(x_542);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_529)) {
 x_591 = lean_alloc_ctor(0, 2, 0);
} else {
 x_591 = x_529;
}
lean_ctor_set(x_591, 0, x_547);
lean_ctor_set(x_591, 1, x_528);
if (lean_is_scalar(x_527)) {
 x_592 = lean_alloc_ctor(0, 2, 0);
} else {
 x_592 = x_527;
}
lean_ctor_set(x_592, 0, x_561);
lean_ctor_set(x_592, 1, x_591);
if (lean_is_scalar(x_525)) {
 x_593 = lean_alloc_ctor(0, 2, 0);
} else {
 x_593 = x_525;
}
lean_ctor_set(x_593, 0, x_575);
lean_ctor_set(x_593, 1, x_592);
x_594 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_594, 0, x_589);
lean_ctor_set(x_594, 1, x_593);
lean_ctor_set(x_20, 1, x_594);
x_595 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_595, 0, x_20);
x_596 = lean_apply_2(x_2, lean_box(0), x_595);
x_597 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_596);
return x_597;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_529);
lean_dec(x_527);
lean_dec(x_525);
lean_free_object(x_20);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_598 = x_28;
} else {
 lean_dec_ref(x_28);
 x_598 = lean_box(0);
}
x_599 = lean_array_fget(x_530, x_531);
lean_dec(x_531);
lean_dec_ref(x_530);
x_600 = lean_array_fget(x_542, x_543);
lean_dec(x_543);
lean_dec_ref(x_542);
x_601 = lean_array_fget(x_557, x_558);
lean_dec(x_558);
lean_dec_ref(x_557);
x_602 = lean_array_fget(x_571, x_572);
lean_dec(x_572);
lean_dec_ref(x_571);
x_603 = lean_array_fget(x_585, x_586);
x_604 = lean_box(x_5);
x_605 = lean_box(x_6);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_9);
x_606 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 15);
lean_closure_set(x_606, 0, x_4);
lean_closure_set(x_606, 1, x_604);
lean_closure_set(x_606, 2, x_605);
lean_closure_set(x_606, 3, x_7);
lean_closure_set(x_606, 4, x_8);
lean_closure_set(x_606, 5, x_17);
lean_closure_set(x_606, 6, x_9);
lean_closure_set(x_606, 7, x_603);
lean_closure_set(x_606, 8, x_10);
lean_closure_set(x_606, 9, x_11);
lean_closure_set(x_606, 10, x_12);
lean_closure_set(x_606, 11, x_13);
lean_closure_set(x_606, 12, x_14);
lean_closure_set(x_606, 13, x_601);
lean_closure_set(x_606, 14, x_599);
x_607 = lean_nat_add(x_586, x_545);
lean_dec(x_586);
if (lean_is_scalar(x_598)) {
 x_608 = lean_alloc_ctor(0, 3, 0);
} else {
 x_608 = x_598;
}
lean_ctor_set(x_608, 0, x_585);
lean_ctor_set(x_608, 1, x_607);
lean_ctor_set(x_608, 2, x_587);
lean_inc(x_9);
x_609 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 10, 9);
lean_closure_set(x_609, 0, x_528);
lean_closure_set(x_609, 1, x_547);
lean_closure_set(x_609, 2, x_561);
lean_closure_set(x_609, 3, x_575);
lean_closure_set(x_609, 4, x_589);
lean_closure_set(x_609, 5, x_608);
lean_closure_set(x_609, 6, x_2);
lean_closure_set(x_609, 7, x_15);
lean_closure_set(x_609, 8, x_9);
x_610 = lean_nat_sub(x_602, x_14);
lean_dec(x_14);
lean_dec(x_602);
x_611 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_13, x_12, x_600, x_610, x_16, x_606);
x_612 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_611, x_609);
x_613 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_612);
return x_613;
}
}
}
}
}
}
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; uint8_t x_626; 
x_614 = lean_ctor_get(x_20, 0);
lean_inc(x_614);
lean_dec(x_20);
x_615 = lean_ctor_get(x_21, 0);
lean_inc(x_615);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_616 = x_21;
} else {
 lean_dec_ref(x_21);
 x_616 = lean_box(0);
}
x_617 = lean_ctor_get(x_22, 0);
lean_inc(x_617);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_618 = x_22;
} else {
 lean_dec_ref(x_22);
 x_618 = lean_box(0);
}
x_619 = lean_ctor_get(x_23, 0);
lean_inc(x_619);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_620 = x_23;
} else {
 lean_dec_ref(x_23);
 x_620 = lean_box(0);
}
x_621 = lean_ctor_get(x_24, 1);
lean_inc(x_621);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_622 = x_24;
} else {
 lean_dec_ref(x_24);
 x_622 = lean_box(0);
}
x_623 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_623);
x_624 = lean_ctor_get(x_25, 1);
lean_inc(x_624);
x_625 = lean_ctor_get(x_25, 2);
lean_inc(x_625);
x_626 = lean_nat_dec_lt(x_624, x_625);
if (x_626 == 0)
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_622)) {
 x_627 = lean_alloc_ctor(0, 2, 0);
} else {
 x_627 = x_622;
}
lean_ctor_set(x_627, 0, x_25);
lean_ctor_set(x_627, 1, x_621);
if (lean_is_scalar(x_620)) {
 x_628 = lean_alloc_ctor(0, 2, 0);
} else {
 x_628 = x_620;
}
lean_ctor_set(x_628, 0, x_619);
lean_ctor_set(x_628, 1, x_627);
if (lean_is_scalar(x_618)) {
 x_629 = lean_alloc_ctor(0, 2, 0);
} else {
 x_629 = x_618;
}
lean_ctor_set(x_629, 0, x_617);
lean_ctor_set(x_629, 1, x_628);
if (lean_is_scalar(x_616)) {
 x_630 = lean_alloc_ctor(0, 2, 0);
} else {
 x_630 = x_616;
}
lean_ctor_set(x_630, 0, x_615);
lean_ctor_set(x_630, 1, x_629);
x_631 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_631, 0, x_614);
lean_ctor_set(x_631, 1, x_630);
x_632 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_632, 0, x_631);
x_633 = lean_apply_2(x_2, lean_box(0), x_632);
x_634 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_633);
return x_634;
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; uint8_t x_642; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_635 = x_25;
} else {
 lean_dec_ref(x_25);
 x_635 = lean_box(0);
}
x_636 = lean_ctor_get(x_619, 0);
lean_inc_ref(x_636);
x_637 = lean_ctor_get(x_619, 1);
lean_inc(x_637);
x_638 = lean_ctor_get(x_619, 2);
lean_inc(x_638);
x_639 = lean_unsigned_to_nat(1u);
x_640 = lean_nat_add(x_624, x_639);
lean_inc_ref(x_623);
if (lean_is_scalar(x_635)) {
 x_641 = lean_alloc_ctor(0, 3, 0);
} else {
 x_641 = x_635;
}
lean_ctor_set(x_641, 0, x_623);
lean_ctor_set(x_641, 1, x_640);
lean_ctor_set(x_641, 2, x_625);
x_642 = lean_nat_dec_lt(x_637, x_638);
if (x_642 == 0)
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; 
lean_dec(x_638);
lean_dec(x_637);
lean_dec_ref(x_636);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_622)) {
 x_643 = lean_alloc_ctor(0, 2, 0);
} else {
 x_643 = x_622;
}
lean_ctor_set(x_643, 0, x_641);
lean_ctor_set(x_643, 1, x_621);
if (lean_is_scalar(x_620)) {
 x_644 = lean_alloc_ctor(0, 2, 0);
} else {
 x_644 = x_620;
}
lean_ctor_set(x_644, 0, x_619);
lean_ctor_set(x_644, 1, x_643);
if (lean_is_scalar(x_618)) {
 x_645 = lean_alloc_ctor(0, 2, 0);
} else {
 x_645 = x_618;
}
lean_ctor_set(x_645, 0, x_617);
lean_ctor_set(x_645, 1, x_644);
if (lean_is_scalar(x_616)) {
 x_646 = lean_alloc_ctor(0, 2, 0);
} else {
 x_646 = x_616;
}
lean_ctor_set(x_646, 0, x_615);
lean_ctor_set(x_646, 1, x_645);
x_647 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_647, 0, x_614);
lean_ctor_set(x_647, 1, x_646);
x_648 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_648, 0, x_647);
x_649 = lean_apply_2(x_2, lean_box(0), x_648);
x_650 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_649);
return x_650;
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; uint8_t x_657; 
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 lean_ctor_release(x_619, 2);
 x_651 = x_619;
} else {
 lean_dec_ref(x_619);
 x_651 = lean_box(0);
}
x_652 = lean_ctor_get(x_617, 0);
lean_inc_ref(x_652);
x_653 = lean_ctor_get(x_617, 1);
lean_inc(x_653);
x_654 = lean_ctor_get(x_617, 2);
lean_inc(x_654);
x_655 = lean_nat_add(x_637, x_639);
lean_inc_ref(x_636);
if (lean_is_scalar(x_651)) {
 x_656 = lean_alloc_ctor(0, 3, 0);
} else {
 x_656 = x_651;
}
lean_ctor_set(x_656, 0, x_636);
lean_ctor_set(x_656, 1, x_655);
lean_ctor_set(x_656, 2, x_638);
x_657 = lean_nat_dec_lt(x_653, x_654);
if (x_657 == 0)
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; 
lean_dec(x_654);
lean_dec(x_653);
lean_dec_ref(x_652);
lean_dec(x_637);
lean_dec_ref(x_636);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_622)) {
 x_658 = lean_alloc_ctor(0, 2, 0);
} else {
 x_658 = x_622;
}
lean_ctor_set(x_658, 0, x_641);
lean_ctor_set(x_658, 1, x_621);
if (lean_is_scalar(x_620)) {
 x_659 = lean_alloc_ctor(0, 2, 0);
} else {
 x_659 = x_620;
}
lean_ctor_set(x_659, 0, x_656);
lean_ctor_set(x_659, 1, x_658);
if (lean_is_scalar(x_618)) {
 x_660 = lean_alloc_ctor(0, 2, 0);
} else {
 x_660 = x_618;
}
lean_ctor_set(x_660, 0, x_617);
lean_ctor_set(x_660, 1, x_659);
if (lean_is_scalar(x_616)) {
 x_661 = lean_alloc_ctor(0, 2, 0);
} else {
 x_661 = x_616;
}
lean_ctor_set(x_661, 0, x_615);
lean_ctor_set(x_661, 1, x_660);
x_662 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_662, 0, x_614);
lean_ctor_set(x_662, 1, x_661);
x_663 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_663, 0, x_662);
x_664 = lean_apply_2(x_2, lean_box(0), x_663);
x_665 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_664);
return x_665;
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; uint8_t x_672; 
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 lean_ctor_release(x_617, 2);
 x_666 = x_617;
} else {
 lean_dec_ref(x_617);
 x_666 = lean_box(0);
}
x_667 = lean_ctor_get(x_615, 0);
lean_inc_ref(x_667);
x_668 = lean_ctor_get(x_615, 1);
lean_inc(x_668);
x_669 = lean_ctor_get(x_615, 2);
lean_inc(x_669);
x_670 = lean_nat_add(x_653, x_639);
lean_inc_ref(x_652);
if (lean_is_scalar(x_666)) {
 x_671 = lean_alloc_ctor(0, 3, 0);
} else {
 x_671 = x_666;
}
lean_ctor_set(x_671, 0, x_652);
lean_ctor_set(x_671, 1, x_670);
lean_ctor_set(x_671, 2, x_654);
x_672 = lean_nat_dec_lt(x_668, x_669);
if (x_672 == 0)
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
lean_dec(x_669);
lean_dec(x_668);
lean_dec_ref(x_667);
lean_dec(x_653);
lean_dec_ref(x_652);
lean_dec(x_637);
lean_dec_ref(x_636);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_622)) {
 x_673 = lean_alloc_ctor(0, 2, 0);
} else {
 x_673 = x_622;
}
lean_ctor_set(x_673, 0, x_641);
lean_ctor_set(x_673, 1, x_621);
if (lean_is_scalar(x_620)) {
 x_674 = lean_alloc_ctor(0, 2, 0);
} else {
 x_674 = x_620;
}
lean_ctor_set(x_674, 0, x_656);
lean_ctor_set(x_674, 1, x_673);
if (lean_is_scalar(x_618)) {
 x_675 = lean_alloc_ctor(0, 2, 0);
} else {
 x_675 = x_618;
}
lean_ctor_set(x_675, 0, x_671);
lean_ctor_set(x_675, 1, x_674);
if (lean_is_scalar(x_616)) {
 x_676 = lean_alloc_ctor(0, 2, 0);
} else {
 x_676 = x_616;
}
lean_ctor_set(x_676, 0, x_615);
lean_ctor_set(x_676, 1, x_675);
x_677 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_677, 0, x_614);
lean_ctor_set(x_677, 1, x_676);
x_678 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_678, 0, x_677);
x_679 = lean_apply_2(x_2, lean_box(0), x_678);
x_680 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_679);
return x_680;
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; uint8_t x_687; 
if (lean_is_exclusive(x_615)) {
 lean_ctor_release(x_615, 0);
 lean_ctor_release(x_615, 1);
 lean_ctor_release(x_615, 2);
 x_681 = x_615;
} else {
 lean_dec_ref(x_615);
 x_681 = lean_box(0);
}
x_682 = lean_ctor_get(x_614, 0);
lean_inc_ref(x_682);
x_683 = lean_ctor_get(x_614, 1);
lean_inc(x_683);
x_684 = lean_ctor_get(x_614, 2);
lean_inc(x_684);
x_685 = lean_nat_add(x_668, x_639);
lean_inc_ref(x_667);
if (lean_is_scalar(x_681)) {
 x_686 = lean_alloc_ctor(0, 3, 0);
} else {
 x_686 = x_681;
}
lean_ctor_set(x_686, 0, x_667);
lean_ctor_set(x_686, 1, x_685);
lean_ctor_set(x_686, 2, x_669);
x_687 = lean_nat_dec_lt(x_683, x_684);
if (x_687 == 0)
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
lean_dec(x_684);
lean_dec(x_683);
lean_dec_ref(x_682);
lean_dec(x_668);
lean_dec_ref(x_667);
lean_dec(x_653);
lean_dec_ref(x_652);
lean_dec(x_637);
lean_dec_ref(x_636);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
if (lean_is_scalar(x_622)) {
 x_688 = lean_alloc_ctor(0, 2, 0);
} else {
 x_688 = x_622;
}
lean_ctor_set(x_688, 0, x_641);
lean_ctor_set(x_688, 1, x_621);
if (lean_is_scalar(x_620)) {
 x_689 = lean_alloc_ctor(0, 2, 0);
} else {
 x_689 = x_620;
}
lean_ctor_set(x_689, 0, x_656);
lean_ctor_set(x_689, 1, x_688);
if (lean_is_scalar(x_618)) {
 x_690 = lean_alloc_ctor(0, 2, 0);
} else {
 x_690 = x_618;
}
lean_ctor_set(x_690, 0, x_671);
lean_ctor_set(x_690, 1, x_689);
if (lean_is_scalar(x_616)) {
 x_691 = lean_alloc_ctor(0, 2, 0);
} else {
 x_691 = x_616;
}
lean_ctor_set(x_691, 0, x_686);
lean_ctor_set(x_691, 1, x_690);
x_692 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_692, 0, x_614);
lean_ctor_set(x_692, 1, x_691);
x_693 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_693, 0, x_692);
x_694 = lean_apply_2(x_2, lean_box(0), x_693);
x_695 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_694);
return x_695;
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
lean_dec(x_622);
lean_dec(x_620);
lean_dec(x_618);
lean_dec(x_616);
if (lean_is_exclusive(x_614)) {
 lean_ctor_release(x_614, 0);
 lean_ctor_release(x_614, 1);
 lean_ctor_release(x_614, 2);
 x_696 = x_614;
} else {
 lean_dec_ref(x_614);
 x_696 = lean_box(0);
}
x_697 = lean_array_fget(x_623, x_624);
lean_dec(x_624);
lean_dec_ref(x_623);
x_698 = lean_array_fget(x_636, x_637);
lean_dec(x_637);
lean_dec_ref(x_636);
x_699 = lean_array_fget(x_652, x_653);
lean_dec(x_653);
lean_dec_ref(x_652);
x_700 = lean_array_fget(x_667, x_668);
lean_dec(x_668);
lean_dec_ref(x_667);
x_701 = lean_array_fget(x_682, x_683);
x_702 = lean_box(x_5);
x_703 = lean_box(x_6);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_9);
x_704 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 15);
lean_closure_set(x_704, 0, x_4);
lean_closure_set(x_704, 1, x_702);
lean_closure_set(x_704, 2, x_703);
lean_closure_set(x_704, 3, x_7);
lean_closure_set(x_704, 4, x_8);
lean_closure_set(x_704, 5, x_17);
lean_closure_set(x_704, 6, x_9);
lean_closure_set(x_704, 7, x_701);
lean_closure_set(x_704, 8, x_10);
lean_closure_set(x_704, 9, x_11);
lean_closure_set(x_704, 10, x_12);
lean_closure_set(x_704, 11, x_13);
lean_closure_set(x_704, 12, x_14);
lean_closure_set(x_704, 13, x_699);
lean_closure_set(x_704, 14, x_697);
x_705 = lean_nat_add(x_683, x_639);
lean_dec(x_683);
if (lean_is_scalar(x_696)) {
 x_706 = lean_alloc_ctor(0, 3, 0);
} else {
 x_706 = x_696;
}
lean_ctor_set(x_706, 0, x_682);
lean_ctor_set(x_706, 1, x_705);
lean_ctor_set(x_706, 2, x_684);
lean_inc(x_9);
x_707 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 10, 9);
lean_closure_set(x_707, 0, x_621);
lean_closure_set(x_707, 1, x_641);
lean_closure_set(x_707, 2, x_656);
lean_closure_set(x_707, 3, x_671);
lean_closure_set(x_707, 4, x_686);
lean_closure_set(x_707, 5, x_706);
lean_closure_set(x_707, 6, x_2);
lean_closure_set(x_707, 7, x_15);
lean_closure_set(x_707, 8, x_9);
x_708 = lean_nat_sub(x_700, x_14);
lean_dec(x_14);
lean_dec(x_700);
x_709 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_13, x_12, x_698, x_708, x_16, x_704);
x_710 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_709, x_707);
x_711 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_3, x_710);
return x_711;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, uint8_t x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23) {
_start:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_24 = l_Std_PRange_instUpwardEnumerableNat;
lean_inc(x_3);
lean_inc(x_2);
x_25 = l_Array_toSubarray___redArg(x_1, x_2, x_3);
x_26 = lean_array_get_size(x_4);
lean_inc(x_2);
x_27 = l_Array_toSubarray___redArg(x_4, x_2, x_26);
x_28 = lean_array_get_size(x_5);
lean_inc(x_2);
x_29 = l_Array_toSubarray___redArg(x_5, x_2, x_28);
x_30 = lean_array_get_size(x_6);
lean_inc(x_2);
x_31 = l_Array_toSubarray___redArg(x_6, x_2, x_30);
x_32 = lean_array_get_size(x_23);
lean_inc(x_2);
x_33 = l_Array_toSubarray___redArg(x_23, x_2, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_7);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_nat_dec_lt(x_2, x_3);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_apply_2(x_8, lean_box(0), x_38);
x_41 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_40, x_10);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__1;
x_43 = lean_box(0);
x_44 = lean_box(x_14);
x_45 = lean_box(x_15);
lean_inc(x_2);
lean_inc_ref(x_21);
lean_inc(x_9);
x_46 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed), 20, 16);
lean_closure_set(x_46, 0, x_11);
lean_closure_set(x_46, 1, x_8);
lean_closure_set(x_46, 2, x_12);
lean_closure_set(x_46, 3, x_13);
lean_closure_set(x_46, 4, x_44);
lean_closure_set(x_46, 5, x_45);
lean_closure_set(x_46, 6, x_16);
lean_closure_set(x_46, 7, x_17);
lean_closure_set(x_46, 8, x_9);
lean_closure_set(x_46, 9, x_18);
lean_closure_set(x_46, 10, x_19);
lean_closure_set(x_46, 11, x_20);
lean_closure_set(x_46, 12, x_21);
lean_closure_set(x_46, 13, x_22);
lean_closure_set(x_46, 14, x_43);
lean_closure_set(x_46, 15, x_2);
x_47 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___redArg(x_24, x_42, x_21, x_3, x_38, x_46, x_2);
x_48 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_47, x_10);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, uint8_t x_23, uint8_t x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33, lean_object* x_34) {
_start:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc(x_13);
lean_inc(x_10);
lean_inc_ref(x_1);
x_35 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__39), 15, 14);
lean_closure_set(x_35, 0, x_33);
lean_closure_set(x_35, 1, x_1);
lean_closure_set(x_35, 2, x_2);
lean_closure_set(x_35, 3, x_3);
lean_closure_set(x_35, 4, x_4);
lean_closure_set(x_35, 5, x_5);
lean_closure_set(x_35, 6, x_6);
lean_closure_set(x_35, 7, x_7);
lean_closure_set(x_35, 8, x_8);
lean_closure_set(x_35, 9, x_9);
lean_closure_set(x_35, 10, x_10);
lean_closure_set(x_35, 11, x_11);
lean_closure_set(x_35, 12, x_12);
lean_closure_set(x_35, 13, x_13);
x_36 = lean_box(x_23);
x_37 = lean_box(x_24);
lean_inc(x_25);
lean_inc(x_13);
lean_inc(x_16);
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed), 23, 22);
lean_closure_set(x_38, 0, x_14);
lean_closure_set(x_38, 1, x_15);
lean_closure_set(x_38, 2, x_16);
lean_closure_set(x_38, 3, x_17);
lean_closure_set(x_38, 4, x_1);
lean_closure_set(x_38, 5, x_18);
lean_closure_set(x_38, 6, x_19);
lean_closure_set(x_38, 7, x_10);
lean_closure_set(x_38, 8, x_13);
lean_closure_set(x_38, 9, x_35);
lean_closure_set(x_38, 10, x_20);
lean_closure_set(x_38, 11, x_21);
lean_closure_set(x_38, 12, x_22);
lean_closure_set(x_38, 13, x_36);
lean_closure_set(x_38, 14, x_37);
lean_closure_set(x_38, 15, x_25);
lean_closure_set(x_38, 16, x_26);
lean_closure_set(x_38, 17, x_27);
lean_closure_set(x_38, 18, x_28);
lean_closure_set(x_38, 19, x_29);
lean_closure_set(x_38, 20, x_30);
lean_closure_set(x_38, 21, x_31);
x_39 = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN), 7, 2);
lean_closure_set(x_39, 0, x_16);
lean_closure_set(x_39, 1, x_32);
x_40 = lean_apply_2(x_25, lean_box(0), x_39);
x_41 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_40, x_38);
return x_41;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3;
x_4 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = l_Lean_indentD(x_2);
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_3, lean_box(0), x_1);
x_10 = l_Lean_Meta_mapErrorImp___redArg(x_9, x_2, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to transform matcher, type error when constructing splitter motive:", 74, 74);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nfailed with", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__1;
lean_inc_ref(x_2);
x_13 = l_Lean_indentExpr(x_2);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
x_14 = l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_check), 6, 1);
lean_closure_set(x_17, 0, x_2);
x_18 = lean_apply_2(x_3, lean_box(0), x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55), 8, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_16);
x_20 = lean_apply_2(x_10, lean_box(0), x_19);
x_21 = lean_apply_1(x_11, lean_box(0));
lean_inc(x_4);
x_22 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_20, x_21);
x_23 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_22, x_5);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_26 = l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__1;
lean_inc_ref(x_2);
x_27 = l_Lean_indentExpr(x_2);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(x_31, 0, x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_Meta_check), 6, 1);
lean_closure_set(x_32, 0, x_2);
x_33 = lean_apply_2(x_3, lean_box(0), x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55), 8, 2);
lean_closure_set(x_34, 0, x_33);
lean_closure_set(x_34, 1, x_31);
x_35 = lean_apply_2(x_24, lean_box(0), x_34);
x_36 = lean_apply_1(x_25, lean_box(0));
lean_inc(x_4);
x_37 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_35, x_36);
x_38 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_37, x_5);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_39 = lean_box(0);
x_40 = lean_apply_2(x_6, lean_box(0), x_39);
x_41 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_40, x_7);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, uint8_t x_22, uint8_t x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32) {
_start:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 2);
lean_inc_ref(x_34);
lean_dec_ref(x_32);
lean_inc(x_33);
x_35 = l_Lean_Expr_const___override(x_33, x_1);
x_36 = l_Lean_mkAppN(x_35, x_2);
lean_inc_ref(x_3);
x_37 = l_Lean_Expr_app___override(x_36, x_3);
x_38 = l_Lean_mkAppN(x_37, x_4);
x_39 = lean_box(x_22);
x_40 = lean_box(x_23);
lean_inc_ref(x_38);
lean_inc_ref(x_28);
lean_inc(x_24);
lean_inc(x_12);
lean_inc(x_9);
x_41 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed), 34, 32);
lean_closure_set(x_41, 0, x_34);
lean_closure_set(x_41, 1, x_5);
lean_closure_set(x_41, 2, x_33);
lean_closure_set(x_41, 3, x_6);
lean_closure_set(x_41, 4, x_7);
lean_closure_set(x_41, 5, x_8);
lean_closure_set(x_41, 6, x_2);
lean_closure_set(x_41, 7, x_3);
lean_closure_set(x_41, 8, x_4);
lean_closure_set(x_41, 9, x_9);
lean_closure_set(x_41, 10, x_10);
lean_closure_set(x_41, 11, x_11);
lean_closure_set(x_41, 12, x_12);
lean_closure_set(x_41, 13, x_13);
lean_closure_set(x_41, 14, x_14);
lean_closure_set(x_41, 15, x_15);
lean_closure_set(x_41, 16, x_16);
lean_closure_set(x_41, 17, x_17);
lean_closure_set(x_41, 18, x_18);
lean_closure_set(x_41, 19, x_19);
lean_closure_set(x_41, 20, x_20);
lean_closure_set(x_41, 21, x_21);
lean_closure_set(x_41, 22, x_39);
lean_closure_set(x_41, 23, x_40);
lean_closure_set(x_41, 24, x_24);
lean_closure_set(x_41, 25, x_25);
lean_closure_set(x_41, 26, x_26);
lean_closure_set(x_41, 27, x_27);
lean_closure_set(x_41, 28, x_28);
lean_closure_set(x_41, 29, x_29);
lean_closure_set(x_41, 30, x_30);
lean_closure_set(x_41, 31, x_38);
x_42 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54), 3, 2);
lean_closure_set(x_42, 0, x_41);
lean_closure_set(x_42, 1, x_31);
lean_inc_ref(x_42);
lean_inc(x_12);
lean_inc(x_24);
lean_inc_ref(x_38);
x_43 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed), 8, 7);
lean_closure_set(x_43, 0, x_28);
lean_closure_set(x_43, 1, x_38);
lean_closure_set(x_43, 2, x_24);
lean_closure_set(x_43, 3, x_12);
lean_closure_set(x_43, 4, x_42);
lean_closure_set(x_43, 5, x_9);
lean_closure_set(x_43, 6, x_42);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_isTypeCorrect), 6, 1);
lean_closure_set(x_44, 0, x_38);
x_45 = lean_apply_2(x_24, lean_box(0), x_44);
x_46 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_45, x_43);
return x_46;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, uint8_t x_21, uint8_t x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32) {
_start:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_box(x_21);
x_34 = lean_box(x_22);
lean_inc(x_23);
lean_inc(x_12);
x_35 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed), 32, 31);
lean_closure_set(x_35, 0, x_1);
lean_closure_set(x_35, 1, x_2);
lean_closure_set(x_35, 2, x_3);
lean_closure_set(x_35, 3, x_4);
lean_closure_set(x_35, 4, x_5);
lean_closure_set(x_35, 5, x_6);
lean_closure_set(x_35, 6, x_7);
lean_closure_set(x_35, 7, x_8);
lean_closure_set(x_35, 8, x_9);
lean_closure_set(x_35, 9, x_10);
lean_closure_set(x_35, 10, x_11);
lean_closure_set(x_35, 11, x_12);
lean_closure_set(x_35, 12, x_13);
lean_closure_set(x_35, 13, x_14);
lean_closure_set(x_35, 14, x_15);
lean_closure_set(x_35, 15, x_16);
lean_closure_set(x_35, 16, x_32);
lean_closure_set(x_35, 17, x_17);
lean_closure_set(x_35, 18, x_18);
lean_closure_set(x_35, 19, x_19);
lean_closure_set(x_35, 20, x_20);
lean_closure_set(x_35, 21, x_33);
lean_closure_set(x_35, 22, x_34);
lean_closure_set(x_35, 23, x_23);
lean_closure_set(x_35, 24, x_24);
lean_closure_set(x_35, 25, x_25);
lean_closure_set(x_35, 26, x_26);
lean_closure_set(x_35, 27, x_27);
lean_closure_set(x_35, 28, x_28);
lean_closure_set(x_35, 29, x_29);
lean_closure_set(x_35, 30, x_30);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_Match_getEquationsFor___boxed), 6, 1);
lean_closure_set(x_36, 0, x_31);
x_37 = lean_apply_2(x_23, lean_box(0), x_36);
x_38 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_37, x_35);
return x_38;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, uint8_t x_20, uint8_t x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32) {
_start:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_array_get_size(x_1);
x_34 = lean_box(x_20);
x_35 = lean_box(x_21);
lean_inc(x_22);
lean_inc(x_33);
lean_inc(x_13);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed), 32, 31);
lean_closure_set(x_36, 0, x_2);
lean_closure_set(x_36, 1, x_3);
lean_closure_set(x_36, 2, x_4);
lean_closure_set(x_36, 3, x_5);
lean_closure_set(x_36, 4, x_6);
lean_closure_set(x_36, 5, x_7);
lean_closure_set(x_36, 6, x_8);
lean_closure_set(x_36, 7, x_9);
lean_closure_set(x_36, 8, x_10);
lean_closure_set(x_36, 9, x_11);
lean_closure_set(x_36, 10, x_12);
lean_closure_set(x_36, 11, x_13);
lean_closure_set(x_36, 12, x_1);
lean_closure_set(x_36, 13, x_14);
lean_closure_set(x_36, 14, x_33);
lean_closure_set(x_36, 15, x_15);
lean_closure_set(x_36, 16, x_16);
lean_closure_set(x_36, 17, x_17);
lean_closure_set(x_36, 18, x_18);
lean_closure_set(x_36, 19, x_19);
lean_closure_set(x_36, 20, x_34);
lean_closure_set(x_36, 21, x_35);
lean_closure_set(x_36, 22, x_22);
lean_closure_set(x_36, 23, x_23);
lean_closure_set(x_36, 24, x_24);
lean_closure_set(x_36, 25, x_25);
lean_closure_set(x_36, 26, x_26);
lean_closure_set(x_36, 27, x_27);
lean_closure_set(x_36, 28, x_28);
lean_closure_set(x_36, 29, x_31);
lean_closure_set(x_36, 30, x_29);
x_37 = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN), 7, 2);
lean_closure_set(x_37, 0, x_33);
lean_closure_set(x_37, 1, x_30);
x_38 = lean_apply_2(x_22, lean_box(0), x_37);
x_39 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_38, x_36);
return x_39;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to transform matcher, type error when constructing new pre-splitter motive:", 82, 82);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__1;
lean_inc_ref(x_2);
x_13 = l_Lean_indentExpr(x_2);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
x_14 = l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_check), 6, 1);
lean_closure_set(x_17, 0, x_2);
x_18 = lean_apply_2(x_3, lean_box(0), x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55), 8, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_16);
x_20 = lean_apply_2(x_10, lean_box(0), x_19);
x_21 = lean_apply_1(x_11, lean_box(0));
lean_inc(x_4);
x_22 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_20, x_21);
x_23 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_22, x_5);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_26 = l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__1;
lean_inc_ref(x_2);
x_27 = l_Lean_indentExpr(x_2);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(x_31, 0, x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_Meta_check), 6, 1);
lean_closure_set(x_32, 0, x_2);
x_33 = lean_apply_2(x_3, lean_box(0), x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55), 8, 2);
lean_closure_set(x_34, 0, x_33);
lean_closure_set(x_34, 1, x_31);
x_35 = lean_apply_2(x_24, lean_box(0), x_34);
x_36 = lean_apply_1(x_25, lean_box(0));
lean_inc(x_4);
x_37 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_35, x_36);
x_38 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_37, x_5);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_39 = lean_box(0);
x_40 = lean_apply_2(x_6, lean_box(0), x_39);
x_41 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_40, x_7);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, uint8_t x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, uint8_t x_27, uint8_t x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33) {
_start:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_35);
x_37 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed), 2, 1);
lean_closure_set(x_37, 0, x_35);
if (x_27 == 0)
{
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
goto block_53;
}
else
{
if (x_28 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_17);
lean_inc_ref(x_1);
x_54 = lean_array_to_list(x_1);
lean_inc(x_54);
lean_inc(x_2);
x_55 = l_Lean_Expr_const___override(x_2, x_54);
x_56 = l_Lean_mkAppN(x_55, x_3);
lean_inc_ref(x_4);
x_57 = l_Lean_Expr_app___override(x_56, x_4);
x_58 = l_Lean_mkAppN(x_57, x_5);
x_59 = lean_box(x_18);
x_60 = lean_box(x_27);
lean_inc_ref(x_58);
lean_inc_ref(x_21);
lean_inc(x_19);
lean_inc(x_12);
lean_inc(x_9);
x_61 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed), 32, 30);
lean_closure_set(x_61, 0, x_13);
lean_closure_set(x_61, 1, x_54);
lean_closure_set(x_61, 2, x_3);
lean_closure_set(x_61, 3, x_4);
lean_closure_set(x_61, 4, x_5);
lean_closure_set(x_61, 5, x_37);
lean_closure_set(x_61, 6, x_1);
lean_closure_set(x_61, 7, x_7);
lean_closure_set(x_61, 8, x_8);
lean_closure_set(x_61, 9, x_9);
lean_closure_set(x_61, 10, x_10);
lean_closure_set(x_61, 11, x_11);
lean_closure_set(x_61, 12, x_12);
lean_closure_set(x_61, 13, x_14);
lean_closure_set(x_61, 14, x_6);
lean_closure_set(x_61, 15, x_15);
lean_closure_set(x_61, 16, x_16);
lean_closure_set(x_61, 17, x_29);
lean_closure_set(x_61, 18, x_30);
lean_closure_set(x_61, 19, x_59);
lean_closure_set(x_61, 20, x_60);
lean_closure_set(x_61, 21, x_19);
lean_closure_set(x_61, 22, x_20);
lean_closure_set(x_61, 23, x_31);
lean_closure_set(x_61, 24, x_35);
lean_closure_set(x_61, 25, x_21);
lean_closure_set(x_61, 26, x_22);
lean_closure_set(x_61, 27, x_32);
lean_closure_set(x_61, 28, x_2);
lean_closure_set(x_61, 29, x_58);
x_62 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 3, 2);
lean_closure_set(x_62, 0, x_61);
lean_closure_set(x_62, 1, x_36);
lean_inc_ref(x_62);
lean_inc(x_12);
lean_inc(x_19);
lean_inc_ref(x_58);
x_63 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__65___boxed), 8, 7);
lean_closure_set(x_63, 0, x_21);
lean_closure_set(x_63, 1, x_58);
lean_closure_set(x_63, 2, x_19);
lean_closure_set(x_63, 3, x_12);
lean_closure_set(x_63, 4, x_62);
lean_closure_set(x_63, 5, x_9);
lean_closure_set(x_63, 6, x_62);
x_64 = lean_alloc_closure((void*)(l_Lean_Meta_isTypeCorrect), 6, 1);
lean_closure_set(x_64, 0, x_58);
x_65 = lean_apply_2(x_19, lean_box(0), x_64);
x_66 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_65, x_63);
return x_66;
}
else
{
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
goto block_53;
}
}
block_53:
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = 1;
lean_inc_ref(x_1);
x_39 = lean_array_to_list(x_1);
lean_inc(x_2);
x_40 = l_Lean_Expr_const___override(x_2, x_39);
x_41 = l_Lean_mkAppN(x_40, x_3);
lean_inc_ref(x_4);
x_42 = l_Lean_Expr_app___override(x_41, x_4);
x_43 = l_Lean_mkAppN(x_42, x_5);
x_44 = lean_box(x_18);
x_45 = lean_box(x_38);
lean_inc_ref(x_43);
lean_inc_ref(x_22);
lean_inc(x_19);
lean_inc(x_12);
lean_inc(x_9);
x_46 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed), 29, 27);
lean_closure_set(x_46, 0, x_6);
lean_closure_set(x_46, 1, x_37);
lean_closure_set(x_46, 2, x_2);
lean_closure_set(x_46, 3, x_1);
lean_closure_set(x_46, 4, x_7);
lean_closure_set(x_46, 5, x_8);
lean_closure_set(x_46, 6, x_3);
lean_closure_set(x_46, 7, x_4);
lean_closure_set(x_46, 8, x_5);
lean_closure_set(x_46, 9, x_9);
lean_closure_set(x_46, 10, x_10);
lean_closure_set(x_46, 11, x_11);
lean_closure_set(x_46, 12, x_12);
lean_closure_set(x_46, 13, x_13);
lean_closure_set(x_46, 14, x_14);
lean_closure_set(x_46, 15, x_15);
lean_closure_set(x_46, 16, x_16);
lean_closure_set(x_46, 17, x_17);
lean_closure_set(x_46, 18, x_44);
lean_closure_set(x_46, 19, x_45);
lean_closure_set(x_46, 20, x_19);
lean_closure_set(x_46, 21, x_20);
lean_closure_set(x_46, 22, x_21);
lean_closure_set(x_46, 23, x_22);
lean_closure_set(x_46, 24, x_23);
lean_closure_set(x_46, 25, x_35);
lean_closure_set(x_46, 26, x_43);
x_47 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 3, 2);
lean_closure_set(x_47, 0, x_46);
lean_closure_set(x_47, 1, x_36);
lean_inc_ref(x_47);
lean_inc(x_12);
lean_inc(x_19);
lean_inc_ref(x_43);
x_48 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed), 5, 4);
lean_closure_set(x_48, 0, x_43);
lean_closure_set(x_48, 1, x_19);
lean_closure_set(x_48, 2, x_12);
lean_closure_set(x_48, 3, x_47);
lean_inc(x_12);
lean_inc_ref(x_43);
x_49 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 10, 9);
lean_closure_set(x_49, 0, x_43);
lean_closure_set(x_49, 1, x_22);
lean_closure_set(x_49, 2, x_24);
lean_closure_set(x_49, 3, x_25);
lean_closure_set(x_49, 4, x_26);
lean_closure_set(x_49, 5, x_12);
lean_closure_set(x_49, 6, x_48);
lean_closure_set(x_49, 7, x_9);
lean_closure_set(x_49, 8, x_47);
x_50 = lean_alloc_closure((void*)(l_Lean_Meta_isTypeCorrect), 6, 1);
lean_closure_set(x_50, 0, x_43);
x_51 = lean_apply_2(x_19, lean_box(0), x_50);
x_52 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_51, x_49);
return x_52;
}
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, uint8_t x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, uint8_t x_24, uint8_t x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32) {
_start:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; 
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__0;
x_35 = lean_box(x_15);
x_36 = lean_box(x_24);
x_37 = lean_box(x_25);
lean_inc_ref(x_19);
lean_inc(x_11);
lean_inc_ref(x_4);
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61___boxed), 33, 32);
lean_closure_set(x_38, 0, x_32);
lean_closure_set(x_38, 1, x_1);
lean_closure_set(x_38, 2, x_2);
lean_closure_set(x_38, 3, x_3);
lean_closure_set(x_38, 4, x_4);
lean_closure_set(x_38, 5, x_5);
lean_closure_set(x_38, 6, x_6);
lean_closure_set(x_38, 7, x_7);
lean_closure_set(x_38, 8, x_8);
lean_closure_set(x_38, 9, x_9);
lean_closure_set(x_38, 10, x_10);
lean_closure_set(x_38, 11, x_11);
lean_closure_set(x_38, 12, x_12);
lean_closure_set(x_38, 13, x_33);
lean_closure_set(x_38, 14, x_34);
lean_closure_set(x_38, 15, x_13);
lean_closure_set(x_38, 16, x_14);
lean_closure_set(x_38, 17, x_35);
lean_closure_set(x_38, 18, x_16);
lean_closure_set(x_38, 19, x_17);
lean_closure_set(x_38, 20, x_18);
lean_closure_set(x_38, 21, x_19);
lean_closure_set(x_38, 22, x_20);
lean_closure_set(x_38, 23, x_21);
lean_closure_set(x_38, 24, x_22);
lean_closure_set(x_38, 25, x_23);
lean_closure_set(x_38, 26, x_36);
lean_closure_set(x_38, 27, x_37);
lean_closure_set(x_38, 28, x_26);
lean_closure_set(x_38, 29, x_27);
lean_closure_set(x_38, 30, x_28);
lean_closure_set(x_38, 31, x_29);
x_39 = l_Array_reverse___redArg(x_30);
x_40 = lean_array_get_size(x_39);
x_41 = l_Array_toSubarray___redArg(x_39, x_33, x_40);
x_42 = l_Array_reverse___redArg(x_4);
x_43 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__1;
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_size(x_42);
x_46 = 0;
x_47 = l_Array_forIn_x27Unsafe_loop___redArg(x_19, x_42, x_31, x_45, x_46, x_44);
x_48 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_47, x_38);
return x_48;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__66(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, uint8_t x_23, uint8_t x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31) {
_start:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_box(x_14);
x_37 = lean_box(x_23);
x_38 = lean_box(x_24);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_5);
x_39 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__62___boxed), 32, 31);
lean_closure_set(x_39, 0, x_1);
lean_closure_set(x_39, 1, x_2);
lean_closure_set(x_39, 2, x_33);
lean_closure_set(x_39, 3, x_3);
lean_closure_set(x_39, 4, x_4);
lean_closure_set(x_39, 5, x_5);
lean_closure_set(x_39, 6, x_6);
lean_closure_set(x_39, 7, x_7);
lean_closure_set(x_39, 8, x_8);
lean_closure_set(x_39, 9, x_9);
lean_closure_set(x_39, 10, x_10);
lean_closure_set(x_39, 11, x_11);
lean_closure_set(x_39, 12, x_12);
lean_closure_set(x_39, 13, x_13);
lean_closure_set(x_39, 14, x_36);
lean_closure_set(x_39, 15, x_15);
lean_closure_set(x_39, 16, x_16);
lean_closure_set(x_39, 17, x_17);
lean_closure_set(x_39, 18, x_18);
lean_closure_set(x_39, 19, x_19);
lean_closure_set(x_39, 20, x_20);
lean_closure_set(x_39, 21, x_21);
lean_closure_set(x_39, 22, x_22);
lean_closure_set(x_39, 23, x_37);
lean_closure_set(x_39, 24, x_38);
lean_closure_set(x_39, 25, x_25);
lean_closure_set(x_39, 26, x_26);
lean_closure_set(x_39, 27, x_27);
lean_closure_set(x_39, 28, x_28);
lean_closure_set(x_39, 29, x_35);
lean_closure_set(x_39, 30, x_29);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_34);
x_40 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63), 2, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_apply_2(x_7, lean_box(0), x_30);
x_42 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_41, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_5, 0);
lean_inc(x_43);
lean_dec(x_5);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63), 2, 1);
lean_closure_set(x_44, 0, x_39);
x_45 = lean_array_set(x_30, x_43, x_34);
lean_dec(x_43);
x_46 = lean_apply_2(x_7, lean_box(0), x_45);
x_47 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_46, x_44);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, uint8_t x_25, uint8_t x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33) {
_start:
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc_ref(x_9);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_33);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__24___boxed), 12, 10);
lean_closure_set(x_34, 0, x_1);
lean_closure_set(x_34, 1, x_2);
lean_closure_set(x_34, 2, x_3);
lean_closure_set(x_34, 3, x_33);
lean_closure_set(x_34, 4, x_4);
lean_closure_set(x_34, 5, x_5);
lean_closure_set(x_34, 6, x_6);
lean_closure_set(x_34, 7, x_7);
lean_closure_set(x_34, 8, x_8);
lean_closure_set(x_34, 9, x_9);
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_box(x_25);
x_38 = lean_box(x_26);
lean_inc_ref(x_5);
lean_inc_ref(x_20);
lean_inc(x_3);
x_39 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__66___boxed), 31, 30);
lean_closure_set(x_39, 0, x_10);
lean_closure_set(x_39, 1, x_11);
lean_closure_set(x_39, 2, x_33);
lean_closure_set(x_39, 3, x_12);
lean_closure_set(x_39, 4, x_13);
lean_closure_set(x_39, 5, x_4);
lean_closure_set(x_39, 6, x_1);
lean_closure_set(x_39, 7, x_14);
lean_closure_set(x_39, 8, x_15);
lean_closure_set(x_39, 9, x_3);
lean_closure_set(x_39, 10, x_16);
lean_closure_set(x_39, 11, x_17);
lean_closure_set(x_39, 12, x_18);
lean_closure_set(x_39, 13, x_36);
lean_closure_set(x_39, 14, x_2);
lean_closure_set(x_39, 15, x_19);
lean_closure_set(x_39, 16, x_20);
lean_closure_set(x_39, 17, x_5);
lean_closure_set(x_39, 18, x_21);
lean_closure_set(x_39, 19, x_22);
lean_closure_set(x_39, 20, x_23);
lean_closure_set(x_39, 21, x_24);
lean_closure_set(x_39, 22, x_37);
lean_closure_set(x_39, 23, x_38);
lean_closure_set(x_39, 24, x_27);
lean_closure_set(x_39, 25, x_9);
lean_closure_set(x_39, 26, x_28);
lean_closure_set(x_39, 27, x_29);
lean_closure_set(x_39, 28, x_30);
lean_closure_set(x_39, 29, x_31);
x_40 = l_Lean_Meta_lambdaTelescope___redArg(x_20, x_5, x_32, x_34, x_35);
x_41 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_40, x_39);
return x_41;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__67(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, uint8_t x_24, uint8_t x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33) {
_start:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_box(x_24);
x_35 = lean_box(x_25);
lean_inc_ref(x_8);
lean_inc_ref(x_5);
lean_inc(x_3);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed), 33, 32);
lean_closure_set(x_36, 0, x_1);
lean_closure_set(x_36, 1, x_2);
lean_closure_set(x_36, 2, x_3);
lean_closure_set(x_36, 3, x_4);
lean_closure_set(x_36, 4, x_5);
lean_closure_set(x_36, 5, x_6);
lean_closure_set(x_36, 6, x_7);
lean_closure_set(x_36, 7, x_8);
lean_closure_set(x_36, 8, x_9);
lean_closure_set(x_36, 9, x_10);
lean_closure_set(x_36, 10, x_33);
lean_closure_set(x_36, 11, x_11);
lean_closure_set(x_36, 12, x_12);
lean_closure_set(x_36, 13, x_13);
lean_closure_set(x_36, 14, x_14);
lean_closure_set(x_36, 15, x_15);
lean_closure_set(x_36, 16, x_16);
lean_closure_set(x_36, 17, x_17);
lean_closure_set(x_36, 18, x_18);
lean_closure_set(x_36, 19, x_19);
lean_closure_set(x_36, 20, x_20);
lean_closure_set(x_36, 21, x_21);
lean_closure_set(x_36, 22, x_22);
lean_closure_set(x_36, 23, x_23);
lean_closure_set(x_36, 24, x_34);
lean_closure_set(x_36, 25, x_35);
lean_closure_set(x_36, 26, x_26);
lean_closure_set(x_36, 27, x_27);
lean_closure_set(x_36, 28, x_28);
lean_closure_set(x_36, 29, x_29);
lean_closure_set(x_36, 30, x_30);
lean_closure_set(x_36, 31, x_31);
x_37 = lean_array_size(x_8);
x_38 = 0;
x_39 = l_Array_mapMUnsafe_map___redArg(x_5, x_32, x_37, x_38, x_8);
x_40 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_39, x_36);
return x_40;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__68(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, uint8_t x_24, uint8_t x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33) {
_start:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_box(x_24);
x_35 = lean_box(x_25);
lean_inc(x_31);
lean_inc_ref(x_5);
lean_inc(x_3);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__67___boxed), 33, 32);
lean_closure_set(x_36, 0, x_1);
lean_closure_set(x_36, 1, x_2);
lean_closure_set(x_36, 2, x_3);
lean_closure_set(x_36, 3, x_4);
lean_closure_set(x_36, 4, x_5);
lean_closure_set(x_36, 5, x_6);
lean_closure_set(x_36, 6, x_7);
lean_closure_set(x_36, 7, x_8);
lean_closure_set(x_36, 8, x_9);
lean_closure_set(x_36, 9, x_10);
lean_closure_set(x_36, 10, x_11);
lean_closure_set(x_36, 11, x_12);
lean_closure_set(x_36, 12, x_13);
lean_closure_set(x_36, 13, x_14);
lean_closure_set(x_36, 14, x_15);
lean_closure_set(x_36, 15, x_16);
lean_closure_set(x_36, 16, x_17);
lean_closure_set(x_36, 17, x_18);
lean_closure_set(x_36, 18, x_19);
lean_closure_set(x_36, 19, x_20);
lean_closure_set(x_36, 20, x_21);
lean_closure_set(x_36, 21, x_22);
lean_closure_set(x_36, 22, x_23);
lean_closure_set(x_36, 23, x_34);
lean_closure_set(x_36, 24, x_35);
lean_closure_set(x_36, 25, x_26);
lean_closure_set(x_36, 26, x_27);
lean_closure_set(x_36, 27, x_33);
lean_closure_set(x_36, 28, x_28);
lean_closure_set(x_36, 29, x_29);
lean_closure_set(x_36, 30, x_30);
lean_closure_set(x_36, 31, x_31);
x_37 = lean_array_size(x_32);
x_38 = 0;
x_39 = l_Array_mapMUnsafe_map___redArg(x_5, x_31, x_37, x_38, x_32);
x_40 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_39, x_36);
return x_40;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__69(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("matcher ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" has no MatchInfo found", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__71(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__1;
x_10 = l_Lean_MessageData_ofName(x_1);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__3;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___redArg(x_2, x_3, x_13);
x_15 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_14, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_16 = lean_ctor_get(x_8, 0);
x_17 = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(x_16);
x_18 = lean_apply_2(x_6, lean_box(0), x_17);
x_19 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_18, x_7);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__72(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, uint8_t x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24) {
_start:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_1, 8);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_1, 9);
lean_inc_ref(x_34);
lean_dec_ref(x_1);
lean_inc(x_25);
x_35 = l_Lean_isCasesOnRecursor(x_24, x_25);
x_36 = lean_box(x_18);
x_37 = lean_box(x_35);
lean_inc(x_25);
lean_inc_ref(x_8);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__68___boxed), 33, 32);
lean_closure_set(x_38, 0, x_2);
lean_closure_set(x_38, 1, x_3);
lean_closure_set(x_38, 2, x_4);
lean_closure_set(x_38, 3, x_28);
lean_closure_set(x_38, 4, x_5);
lean_closure_set(x_38, 5, x_6);
lean_closure_set(x_38, 6, x_7);
lean_closure_set(x_38, 7, x_31);
lean_closure_set(x_38, 8, x_8);
lean_closure_set(x_38, 9, x_25);
lean_closure_set(x_38, 10, x_32);
lean_closure_set(x_38, 11, x_27);
lean_closure_set(x_38, 12, x_9);
lean_closure_set(x_38, 13, x_34);
lean_closure_set(x_38, 14, x_33);
lean_closure_set(x_38, 15, x_10);
lean_closure_set(x_38, 16, x_11);
lean_closure_set(x_38, 17, x_12);
lean_closure_set(x_38, 18, x_13);
lean_closure_set(x_38, 19, x_14);
lean_closure_set(x_38, 20, x_15);
lean_closure_set(x_38, 21, x_16);
lean_closure_set(x_38, 22, x_17);
lean_closure_set(x_38, 23, x_36);
lean_closure_set(x_38, 24, x_37);
lean_closure_set(x_38, 25, x_19);
lean_closure_set(x_38, 26, x_20);
lean_closure_set(x_38, 27, x_21);
lean_closure_set(x_38, 28, x_26);
lean_closure_set(x_38, 29, x_30);
lean_closure_set(x_38, 30, x_22);
lean_closure_set(x_38, 31, x_29);
if (x_35 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__69), 2, 1);
lean_closure_set(x_39, 0, x_38);
lean_inc_ref(x_39);
lean_inc(x_4);
lean_inc_ref(x_5);
lean_inc(x_25);
x_40 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__71___boxed), 8, 7);
lean_closure_set(x_40, 0, x_25);
lean_closure_set(x_40, 1, x_5);
lean_closure_set(x_40, 2, x_8);
lean_closure_set(x_40, 3, x_4);
lean_closure_set(x_40, 4, x_39);
lean_closure_set(x_40, 5, x_2);
lean_closure_set(x_40, 6, x_39);
x_41 = l_Lean_Meta_getMatcherInfo_x3f___redArg(x_5, x_23, x_25);
x_42 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_41, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
x_43 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__69), 2, 1);
lean_closure_set(x_43, 0, x_38);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_apply_2(x_2, lean_box(0), x_44);
x_46 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_45, x_43);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec_ref(x_16);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed), 1, 0);
lean_inc(x_1);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_22, 0, x_1);
lean_inc_ref(x_3);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed), 4, 2);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__3___boxed), 1, 0);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__4___boxed), 3, 2);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_4);
x_26 = lean_box(x_11);
lean_inc(x_1);
lean_inc(x_17);
lean_inc(x_20);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed), 7, 4);
lean_closure_set(x_27, 0, x_20);
lean_closure_set(x_27, 1, x_17);
lean_closure_set(x_27, 2, x_26);
lean_closure_set(x_27, 3, x_1);
lean_inc(x_1);
lean_inc(x_17);
lean_inc(x_20);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16), 6, 3);
lean_closure_set(x_28, 0, x_20);
lean_closure_set(x_28, 1, x_17);
lean_closure_set(x_28, 2, x_1);
x_29 = lean_box(x_10);
lean_inc(x_17);
x_30 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__72___boxed), 24, 23);
lean_closure_set(x_30, 0, x_9);
lean_closure_set(x_30, 1, x_20);
lean_closure_set(x_30, 2, x_1);
lean_closure_set(x_30, 3, x_17);
lean_closure_set(x_30, 4, x_3);
lean_closure_set(x_30, 5, x_27);
lean_closure_set(x_30, 6, x_13);
lean_closure_set(x_30, 7, x_4);
lean_closure_set(x_30, 8, x_15);
lean_closure_set(x_30, 9, x_19);
lean_closure_set(x_30, 10, x_21);
lean_closure_set(x_30, 11, x_14);
lean_closure_set(x_30, 12, x_2);
lean_closure_set(x_30, 13, x_23);
lean_closure_set(x_30, 14, x_6);
lean_closure_set(x_30, 15, x_7);
lean_closure_set(x_30, 16, x_8);
lean_closure_set(x_30, 17, x_29);
lean_closure_set(x_30, 18, x_24);
lean_closure_set(x_30, 19, x_25);
lean_closure_set(x_30, 20, x_28);
lean_closure_set(x_30, 21, x_12);
lean_closure_set(x_30, 22, x_5);
x_31 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_18, x_30);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_MatcherApp_transform___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_MatcherApp_transform___redArg___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_MatcherApp_transform___redArg___lam__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_MatcherApp_transform___redArg___lam__2(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_MatcherApp_transform___redArg___lam__3(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_MatcherApp_transform___redArg___lam__4(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_MatcherApp_transform___redArg___lam__5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_transform___redArg___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_MatcherApp_transform___redArg___lam__7(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_transform___redArg___lam__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Meta_MatcherApp_transform___redArg___lam__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__10(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_MatcherApp_transform___redArg___lam__12(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_MatcherApp_transform___redArg___lam__13(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_transform___redArg___lam__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__15(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_MatcherApp_transform___redArg___lam__21(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_MatcherApp_transform___redArg___lam__24(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_MatcherApp_transform___redArg___lam__23(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_MatcherApp_transform___redArg___lam__25(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
x_8 = lean_unbox(x_4);
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__27(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
x_15 = lean_unbox(x_3);
x_16 = l_Lean_Meta_MatcherApp_transform___redArg___lam__30(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_1);
x_15 = lean_unbox(x_2);
x_16 = l_Lean_Meta_MatcherApp_transform___redArg___lam__31(x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_MatcherApp_transform___redArg___lam__32(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_4);
x_19 = lean_unbox(x_5);
x_20 = l_Lean_Meta_MatcherApp_transform___redArg___lam__34(x_1, x_2, x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox(x_11);
x_21 = lean_unbox(x_12);
x_22 = l_Lean_Meta_MatcherApp_transform___redArg___lam__35(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20, x_21, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
_start:
{
uint8_t x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_unbox(x_19);
x_31 = lean_unbox(x_20);
x_32 = l_Lean_Meta_MatcherApp_transform___redArg___lam__36(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_30, x_31, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
return x_32;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_MatcherApp_transform___redArg___lam__38(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_MatcherApp_transform___redArg___lam__41(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_5);
x_10 = lean_unbox(x_6);
x_11 = l_Lean_Meta_MatcherApp_transform___redArg___lam__42(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_5);
x_17 = lean_unbox(x_6);
x_18 = l_Lean_Meta_MatcherApp_transform___redArg___lam__44(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_4);
x_19 = lean_unbox(x_5);
x_20 = l_Lean_Meta_MatcherApp_transform___redArg___lam__45(x_1, x_2, x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_3);
x_19 = lean_unbox(x_4);
x_20 = l_Lean_Meta_MatcherApp_transform___redArg___lam__46(x_1, x_2, x_18, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__47(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_2);
x_19 = lean_unbox(x_3);
x_20 = l_Lean_Meta_MatcherApp_transform___redArg___lam__48(x_1, x_18, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__49(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_unbox(x_5);
x_22 = lean_unbox(x_6);
x_23 = l_Lean_Meta_MatcherApp_transform___redArg___lam__51(x_1, x_2, x_3, x_4, x_21, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
_start:
{
uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_unbox(x_14);
x_25 = lean_unbox(x_15);
x_26 = l_Lean_Meta_MatcherApp_transform___redArg___lam__52(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_24, x_25, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
lean_object* x_33 = _args[32];
lean_object* x_34 = _args[33];
_start:
{
uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_35 = lean_unbox(x_23);
x_36 = lean_unbox(x_24);
x_37 = l_Lean_Meta_MatcherApp_transform___redArg___lam__53(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_35, x_36, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
return x_37;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Meta_MatcherApp_transform___redArg___lam__57(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
_start:
{
uint8_t x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_unbox(x_22);
x_34 = lean_unbox(x_23);
x_35 = l_Lean_Meta_MatcherApp_transform___redArg___lam__58(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_33, x_34, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
return x_35;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
_start:
{
uint8_t x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_unbox(x_21);
x_34 = lean_unbox(x_22);
x_35 = l_Lean_Meta_MatcherApp_transform___redArg___lam__59(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_33, x_34, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
return x_35;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
_start:
{
uint8_t x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_unbox(x_20);
x_34 = lean_unbox(x_21);
x_35 = l_Lean_Meta_MatcherApp_transform___redArg___lam__60(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_33, x_34, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
return x_35;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Meta_MatcherApp_transform___redArg___lam__65(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
lean_object* x_33 = _args[32];
_start:
{
uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_34 = lean_unbox(x_18);
x_35 = lean_unbox(x_27);
x_36 = lean_unbox(x_28);
x_37 = l_Lean_Meta_MatcherApp_transform___redArg___lam__61(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_34, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_35, x_36, x_29, x_30, x_31, x_32, x_33);
return x_37;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
_start:
{
uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_33 = lean_unbox(x_15);
x_34 = lean_unbox(x_24);
x_35 = lean_unbox(x_25);
x_36 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_33, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_34, x_35, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
return x_36;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__66___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
_start:
{
uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; 
x_32 = lean_unbox(x_14);
x_33 = lean_unbox(x_23);
x_34 = lean_unbox(x_24);
x_35 = l_Lean_Meta_MatcherApp_transform___redArg___lam__66(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_32, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_33, x_34, x_25, x_26, x_27, x_28, x_29, x_30, x_31);
return x_35;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
lean_object* x_33 = _args[32];
_start:
{
uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_unbox(x_25);
x_35 = lean_unbox(x_26);
x_36 = l_Lean_Meta_MatcherApp_transform___redArg___lam__64(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_34, x_35, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
return x_36;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__67___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
lean_object* x_33 = _args[32];
_start:
{
uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_unbox(x_24);
x_35 = lean_unbox(x_25);
x_36 = l_Lean_Meta_MatcherApp_transform___redArg___lam__67(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_34, x_35, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
return x_36;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__68___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
lean_object* x_33 = _args[32];
_start:
{
uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_unbox(x_24);
x_35 = lean_unbox(x_25);
x_36 = l_Lean_Meta_MatcherApp_transform___redArg___lam__68(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_34, x_35, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
return x_36;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__71___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__71(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__72___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
_start:
{
uint8_t x_25; lean_object* x_26; 
x_25 = lean_unbox(x_18);
x_26 = l_Lean_Meta_MatcherApp_transform___redArg___lam__72(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_25, x_19, x_20, x_21, x_22, x_23, x_24);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_10);
x_17 = lean_unbox(x_11);
x_18 = l_Lean_Meta_MatcherApp_transform___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16, x_17, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_11);
x_18 = lean_unbox(x_12);
x_19 = l_Lean_Meta_MatcherApp_transform(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17, x_18, x_13, x_14, x_15, x_16);
return x_19;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_hasFVar(x_2);
if (x_3 == 0)
{
return x_3;
}
else
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = l_Lean_Expr_fvarId_x21(x_1);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_10);
return x_11;
}
case 5:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0(x_1, x_12);
if (x_14 == 0)
{
x_2 = x_13;
goto _start;
}
else
{
return x_3;
}
}
case 6:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 2);
x_4 = x_16;
x_5 = x_17;
goto block_8;
}
case 7:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_4 = x_18;
x_5 = x_19;
goto block_8;
}
case 8:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_ctor_get(x_2, 3);
x_23 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0(x_1, x_20);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0(x_1, x_21);
if (x_24 == 0)
{
x_2 = x_22;
goto _start;
}
else
{
return x_3;
}
}
else
{
return x_3;
}
}
case 10:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_2, 1);
x_2 = x_26;
goto _start;
}
case 11:
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 2);
x_2 = x_28;
goto _start;
}
default: 
{
uint8_t x_30; 
x_30 = 0;
return x_30;
}
}
}
block_8:
{
uint8_t x_6; 
x_6 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_3;
}
}
}
}
static lean_object* _init_l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Type ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" of alternative ", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" still depends on ", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_1);
x_12 = lean_apply_1(x_1, x_5);
switch (lean_obj_tag(x_12)) {
case 0:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0(x_15, x_2);
if (x_16 == 0)
{
lean_free_object(x_12);
lean_dec(x_15);
{
lean_object* _tmp_4 = x_14;
lean_object* _tmp_5 = x_3;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_14);
lean_dec(x_1);
x_18 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__1;
x_19 = l_Lean_MessageData_ofExpr(x_2);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_18);
x_20 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__3;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_MessageData_ofExpr(x_4);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__5;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_MessageData_ofExpr(x_15);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_29, x_7, x_8, x_9, x_10, x_11);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0(x_32, x_2);
if (x_33 == 0)
{
lean_dec(x_32);
{
lean_object* _tmp_4 = x_31;
lean_object* _tmp_5 = x_3;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_31);
lean_dec(x_1);
x_35 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__1;
x_36 = l_Lean_MessageData_ofExpr(x_2);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__3;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_MessageData_ofExpr(x_4);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__5;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_MessageData_ofExpr(x_32);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_47, x_7, x_8, x_9, x_10, x_11);
return x_48;
}
}
}
case 1:
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_12, 0);
lean_inc(x_49);
lean_dec(x_12);
x_5 = x_49;
goto _start;
}
default: 
{
lean_object* x_51; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_6);
lean_ctor_set(x_51, 1, x_11);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_1);
x_12 = lean_apply_1(x_1, x_5);
switch (lean_obj_tag(x_12)) {
case 0:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0(x_15, x_2);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_12);
lean_dec(x_15);
x_17 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_14, x_3, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_14);
lean_dec(x_1);
x_18 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__1;
x_19 = l_Lean_MessageData_ofExpr(x_2);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_18);
x_20 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__3;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_MessageData_ofExpr(x_4);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__5;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_MessageData_ofExpr(x_15);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_29, x_7, x_8, x_9, x_10, x_11);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0(x_32, x_2);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_32);
x_34 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_31, x_3, x_7, x_8, x_9, x_10, x_11);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_31);
lean_dec(x_1);
x_35 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__1;
x_36 = l_Lean_MessageData_ofExpr(x_2);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__3;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_MessageData_ofExpr(x_4);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__5;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_MessageData_ofExpr(x_32);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_47, x_7, x_8, x_9, x_10, x_11);
return x_48;
}
}
}
case 1:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_12, 0);
lean_inc(x_49);
lean_dec(x_12);
x_50 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_49, x_6, x_7, x_8, x_9, x_10, x_11);
return x_50;
}
default: 
{
lean_object* x_51; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_6);
lean_ctor_set(x_51, 1, x_11);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_fget(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PRange_instUpwardEnumerableNat;
x_2 = l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__1;
x_3 = lean_alloc_closure((void*)(l_Std_PRange_instIteratorRangeIteratorIdOfUpwardEnumerableOfSupportsUpperBound___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1___closed__0;
x_2 = l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__9;
x_3 = l_Std_Iterators_Types_Attach_instIterator___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_68; uint8_t x_69; 
x_15 = lean_box(0);
x_16 = lean_array_get_size(x_8);
x_61 = lean_nat_sub(x_16, x_7);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_nat_dec_le(x_61, x_16);
if (x_69 == 0)
{
lean_inc(x_16);
x_62 = x_68;
x_63 = x_16;
goto block_67;
}
else
{
lean_inc(x_61);
x_62 = x_68;
x_63 = x_61;
goto block_67;
}
block_60:
{
lean_object* x_19; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_19 = lean_infer_type(x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = l_Array_toSubarray___redArg(x_8, x_18, x_16);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 2);
lean_inc(x_25);
x_26 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_26, 0, x_23);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_19, 1, x_25);
lean_ctor_set(x_19, 0, x_27);
x_28 = l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__9;
x_29 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1___closed__1;
x_30 = l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(x_1, x_29, x_28);
x_31 = l_Std_Iterators_instIteratorMap___redArg(x_28, x_30, x_2, x_26);
lean_inc(x_21);
x_32 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1___redArg(x_31, x_21, x_15, x_3, x_19, x_15, x_10, x_11, x_12, x_13, x_22);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Array_ofSubarray___redArg(x_17);
x_35 = l_Lean_Meta_mkLambdaFVars(x_34, x_21, x_4, x_5, x_4, x_5, x_6, x_10, x_11, x_12, x_13, x_33);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_21);
lean_dec_ref(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_40 = lean_ctor_get(x_19, 0);
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_19);
x_42 = l_Array_toSubarray___redArg(x_8, x_18, x_16);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 2);
lean_inc(x_44);
x_45 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_45, 0, x_42);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
x_48 = l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__9;
x_49 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1___closed__1;
x_50 = l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(x_1, x_49, x_48);
x_51 = l_Std_Iterators_instIteratorMap___redArg(x_48, x_50, x_2, x_45);
lean_inc(x_40);
x_52 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1___redArg(x_51, x_40, x_15, x_3, x_47, x_15, x_10, x_11, x_12, x_13, x_41);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = l_Array_ofSubarray___redArg(x_17);
x_55 = l_Lean_Meta_mkLambdaFVars(x_54, x_40, x_4, x_5, x_4, x_5, x_6, x_10, x_11, x_12, x_13, x_53);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_40);
lean_dec_ref(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_58 = x_52;
} else {
 lean_dec_ref(x_52);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
block_67:
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_inc_ref(x_8);
x_64 = l_Array_toSubarray___redArg(x_8, x_62, x_63);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_dec_le(x_61, x_65);
if (x_66 == 0)
{
x_17 = x_64;
x_18 = x_61;
goto block_60;
}
else
{
lean_dec(x_61);
x_17 = x_64;
x_18 = x_65;
goto block_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_8, x_7);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_array_uget(x_9, x_8);
x_18 = lean_box(x_4);
x_19 = lean_box(x_5);
x_20 = lean_box(x_6);
lean_inc(x_1);
lean_inc(x_17);
lean_inc(x_3);
lean_inc(x_2);
x_21 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1___boxed), 14, 7);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_17);
lean_closure_set(x_21, 3, x_18);
lean_closure_set(x_21, 4, x_19);
lean_closure_set(x_21, 5, x_20);
lean_closure_set(x_21, 6, x_1);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_22 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_17, x_21, x_4, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_uset(x_9, x_8, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_8, x_27);
x_29 = lean_array_uset(x_26, x_8, x_23);
x_8 = x_28;
x_9 = x_29;
x_14 = x_24;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_10, x_9);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_array_uget(x_11, x_10);
x_20 = lean_box(x_6);
x_21 = lean_box(x_7);
x_22 = lean_box(x_8);
lean_inc(x_1);
lean_inc(x_19);
lean_inc(x_5);
lean_inc(x_4);
x_23 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1___boxed), 14, 7);
lean_closure_set(x_23, 0, x_4);
lean_closure_set(x_23, 1, x_5);
lean_closure_set(x_23, 2, x_19);
lean_closure_set(x_23, 3, x_20);
lean_closure_set(x_23, 4, x_21);
lean_closure_set(x_23, 5, x_22);
lean_closure_set(x_23, 6, x_1);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_24 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_19, x_23, x_6, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_uset(x_11, x_10, x_27);
x_29 = 1;
x_30 = lean_usize_add(x_10, x_29);
x_31 = lean_array_uset(x_28, x_10, x_25);
x_32 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_30, x_31, x_12, x_13, x_14, x_15, x_26);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_24);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__5___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_uget(x_3, x_2);
x_11 = l_Lean_Expr_fvarId_x21(x_10);
lean_dec(x_10);
lean_inc_ref(x_4);
x_12 = l_Lean_FVarId_getUserName___redArg(x_11, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_16, x_2, x_13);
x_2 = x_18;
x_3 = x_19;
x_7 = x_14;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__5(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__5___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_4, x_3);
lean_inc(x_1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_13 = lean_apply_6(x_1, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_4, x_3, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = lean_array_uset(x_17, x_3, x_14);
x_3 = x_19;
x_4 = x_20;
x_9 = x_15;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__7(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_4, x_3);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_24 = x_5;
} else {
 lean_dec_ref(x_5);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_27 = x_20;
} else {
 lean_dec_ref(x_20);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_21, 2);
lean_inc(x_30);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_27)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_27;
}
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_26);
if (lean_is_scalar(x_22)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_22;
}
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
if (lean_is_scalar(x_24)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_24;
}
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_10);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_37 = lean_ctor_get(x_21, 2);
lean_dec(x_37);
x_38 = lean_ctor_get(x_21, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_21, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_23, 2);
lean_inc(x_42);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_29, x_43);
lean_inc_ref(x_28);
lean_ctor_set(x_21, 1, x_44);
x_45 = lean_nat_dec_lt(x_41, x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_27)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_27;
}
lean_ctor_set(x_46, 0, x_25);
lean_ctor_set(x_46, 1, x_26);
if (lean_is_scalar(x_22)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_22;
}
lean_ctor_set(x_47, 0, x_21);
lean_ctor_set(x_47, 1, x_46);
if (lean_is_scalar(x_24)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_24;
}
lean_ctor_set(x_48, 0, x_23);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_10);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_23);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_23, 2);
lean_dec(x_51);
x_52 = lean_ctor_get(x_23, 1);
lean_dec(x_52);
x_53 = lean_ctor_get(x_23, 0);
lean_dec(x_53);
x_54 = lean_nat_add(x_41, x_43);
lean_inc_ref(x_40);
lean_ctor_set(x_23, 1, x_54);
if (x_1 == 0)
{
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_29);
lean_dec_ref(x_28);
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_array_fget(x_28, x_29);
lean_dec(x_29);
lean_dec_ref(x_28);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_22);
x_62 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_62);
x_63 = l_Lean_Meta_isProof(x_62, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec_ref(x_63);
x_67 = lean_array_fget(x_40, x_41);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_68 = l_Lean_Meta_mkEqHEq(x_67, x_62, x_6, x_7, x_8, x_9, x_66);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
lean_inc(x_69);
x_71 = l_Lean_mkArrow___redArg(x_69, x_26, x_9, x_70);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
x_75 = l_Lean_Expr_isHEq(x_69);
lean_dec(x_69);
x_76 = lean_box(x_75);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_array_push(x_25, x_77);
lean_ctor_set(x_71, 1, x_73);
lean_ctor_set(x_71, 0, x_78);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_21);
lean_ctor_set(x_79, 1, x_71);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_23);
lean_ctor_set(x_80, 1, x_79);
x_11 = x_80;
x_12 = x_74;
goto block_16;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_81 = lean_ctor_get(x_71, 0);
x_82 = lean_ctor_get(x_71, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_71);
x_83 = l_Lean_Expr_isHEq(x_69);
lean_dec(x_69);
x_84 = lean_box(x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_array_push(x_25, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_81);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_21);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_23);
lean_ctor_set(x_89, 1, x_88);
x_11 = x_89;
x_12 = x_82;
goto block_16;
}
}
else
{
uint8_t x_90; 
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_90 = !lean_is_exclusive(x_68);
if (x_90 == 0)
{
return x_68;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_68, 0);
x_92 = lean_ctor_get(x_68, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_68);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec_ref(x_62);
lean_dec(x_41);
lean_dec_ref(x_40);
x_94 = lean_ctor_get(x_63, 1);
lean_inc(x_94);
lean_dec_ref(x_63);
x_95 = lean_box(0);
x_96 = lean_array_push(x_25, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_26);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_21);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_23);
lean_ctor_set(x_99, 1, x_98);
x_11 = x_99;
x_12 = x_94;
goto block_16;
}
}
else
{
uint8_t x_100; 
lean_dec_ref(x_62);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_100 = !lean_is_exclusive(x_63);
if (x_100 == 0)
{
return x_63;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_63, 0);
x_102 = lean_ctor_get(x_63, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_63);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_dec(x_61);
lean_dec(x_41);
lean_dec_ref(x_40);
goto block_60;
}
}
block_60:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_box(0);
x_56 = lean_array_push(x_25, x_55);
if (lean_is_scalar(x_27)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_27;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_26);
if (lean_is_scalar(x_22)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_22;
}
lean_ctor_set(x_58, 0, x_21);
lean_ctor_set(x_58, 1, x_57);
if (lean_is_scalar(x_24)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_24;
}
lean_ctor_set(x_59, 0, x_23);
lean_ctor_set(x_59, 1, x_58);
x_11 = x_59;
x_12 = x_10;
goto block_16;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_23);
x_104 = lean_nat_add(x_41, x_43);
lean_inc_ref(x_40);
x_105 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_105, 0, x_40);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_105, 2, x_42);
if (x_1 == 0)
{
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_29);
lean_dec_ref(x_28);
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_array_fget(x_28, x_29);
lean_dec(x_29);
lean_dec_ref(x_28);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_22);
x_113 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_113);
x_114 = l_Lean_Meta_isProof(x_113, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec_ref(x_114);
x_118 = lean_array_fget(x_40, x_41);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_119 = l_Lean_Meta_mkEqHEq(x_118, x_113, x_6, x_7, x_8, x_9, x_117);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec_ref(x_119);
lean_inc(x_120);
x_122 = l_Lean_mkArrow___redArg(x_120, x_26, x_9, x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
x_126 = l_Lean_Expr_isHEq(x_120);
lean_dec(x_120);
x_127 = lean_box(x_126);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_array_push(x_25, x_128);
if (lean_is_scalar(x_125)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_125;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_123);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_21);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_105);
lean_ctor_set(x_132, 1, x_131);
x_11 = x_132;
x_12 = x_124;
goto block_16;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec_ref(x_105);
lean_dec_ref(x_21);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_133 = lean_ctor_get(x_119, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_119, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_135 = x_119;
} else {
 lean_dec_ref(x_119);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec_ref(x_113);
lean_dec(x_41);
lean_dec_ref(x_40);
x_137 = lean_ctor_get(x_114, 1);
lean_inc(x_137);
lean_dec_ref(x_114);
x_138 = lean_box(0);
x_139 = lean_array_push(x_25, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_26);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_21);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_105);
lean_ctor_set(x_142, 1, x_141);
x_11 = x_142;
x_12 = x_137;
goto block_16;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec_ref(x_113);
lean_dec_ref(x_105);
lean_dec_ref(x_21);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_143 = lean_ctor_get(x_114, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_114, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_145 = x_114;
} else {
 lean_dec_ref(x_114);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_dec(x_112);
lean_dec(x_41);
lean_dec_ref(x_40);
goto block_111;
}
}
block_111:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_box(0);
x_107 = lean_array_push(x_25, x_106);
if (lean_is_scalar(x_27)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_27;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_26);
if (lean_is_scalar(x_22)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_22;
}
lean_ctor_set(x_109, 0, x_21);
lean_ctor_set(x_109, 1, x_108);
if (lean_is_scalar(x_24)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_24;
}
lean_ctor_set(x_110, 0, x_105);
lean_ctor_set(x_110, 1, x_109);
x_11 = x_110;
x_12 = x_10;
goto block_16;
}
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
lean_dec(x_21);
x_147 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_147);
x_148 = lean_ctor_get(x_23, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_23, 2);
lean_inc(x_149);
x_150 = lean_unsigned_to_nat(1u);
x_151 = lean_nat_add(x_29, x_150);
lean_inc_ref(x_28);
x_152 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_152, 0, x_28);
lean_ctor_set(x_152, 1, x_151);
lean_ctor_set(x_152, 2, x_30);
x_153 = lean_nat_dec_lt(x_148, x_149);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_149);
lean_dec(x_148);
lean_dec_ref(x_147);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_is_scalar(x_27)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_27;
}
lean_ctor_set(x_154, 0, x_25);
lean_ctor_set(x_154, 1, x_26);
if (lean_is_scalar(x_22)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_22;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_154);
if (lean_is_scalar(x_24)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_24;
}
lean_ctor_set(x_156, 0, x_23);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_10);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_158 = x_23;
} else {
 lean_dec_ref(x_23);
 x_158 = lean_box(0);
}
x_159 = lean_nat_add(x_148, x_150);
lean_inc_ref(x_147);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(0, 3, 0);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_147);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set(x_160, 2, x_149);
if (x_1 == 0)
{
lean_dec(x_148);
lean_dec_ref(x_147);
lean_dec(x_29);
lean_dec_ref(x_28);
goto block_166;
}
else
{
lean_object* x_167; 
x_167 = lean_array_fget(x_28, x_29);
lean_dec(x_29);
lean_dec_ref(x_28);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_22);
x_168 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_168);
x_169 = l_Lean_Meta_isProof(x_168, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_unbox(x_170);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec_ref(x_169);
x_173 = lean_array_fget(x_147, x_148);
lean_dec(x_148);
lean_dec_ref(x_147);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_174 = l_Lean_Meta_mkEqHEq(x_173, x_168, x_6, x_7, x_8, x_9, x_172);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec_ref(x_174);
lean_inc(x_175);
x_177 = l_Lean_mkArrow___redArg(x_175, x_26, x_9, x_176);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_180 = x_177;
} else {
 lean_dec_ref(x_177);
 x_180 = lean_box(0);
}
x_181 = l_Lean_Expr_isHEq(x_175);
lean_dec(x_175);
x_182 = lean_box(x_181);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_182);
x_184 = lean_array_push(x_25, x_183);
if (lean_is_scalar(x_180)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_180;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_178);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_152);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_160);
lean_ctor_set(x_187, 1, x_186);
x_11 = x_187;
x_12 = x_179;
goto block_16;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec_ref(x_160);
lean_dec_ref(x_152);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_188 = lean_ctor_get(x_174, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_174, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_190 = x_174;
} else {
 lean_dec_ref(x_174);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec_ref(x_168);
lean_dec(x_148);
lean_dec_ref(x_147);
x_192 = lean_ctor_get(x_169, 1);
lean_inc(x_192);
lean_dec_ref(x_169);
x_193 = lean_box(0);
x_194 = lean_array_push(x_25, x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_26);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_152);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_160);
lean_ctor_set(x_197, 1, x_196);
x_11 = x_197;
x_12 = x_192;
goto block_16;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec_ref(x_168);
lean_dec_ref(x_160);
lean_dec_ref(x_152);
lean_dec(x_148);
lean_dec_ref(x_147);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_198 = lean_ctor_get(x_169, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_169, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_200 = x_169;
} else {
 lean_dec_ref(x_169);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
else
{
lean_dec(x_167);
lean_dec(x_148);
lean_dec_ref(x_147);
goto block_166;
}
}
block_166:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_box(0);
x_162 = lean_array_push(x_25, x_161);
if (lean_is_scalar(x_27)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_27;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_26);
if (lean_is_scalar(x_22)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_22;
}
lean_ctor_set(x_164, 0, x_152);
lean_ctor_set(x_164, 1, x_163);
if (lean_is_scalar(x_24)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_24;
}
lean_ctor_set(x_165, 0, x_160);
lean_ctor_set(x_165, 1, x_164);
x_11 = x_165;
x_12 = x_10;
goto block_16;
}
}
}
}
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_4, x_13);
x_4 = x_14;
x_5 = x_11;
x_10 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_3, x_2);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_20 = x_4;
} else {
 lean_dec_ref(x_4);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_23 = x_18;
} else {
 lean_dec_ref(x_18);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_19, 2);
lean_inc(x_26);
x_27 = lean_nat_dec_lt(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
if (lean_is_scalar(x_23)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_23;
}
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_22);
if (lean_is_scalar(x_20)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_20;
}
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_9);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_19, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_19, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_19, 0);
lean_dec(x_34);
x_35 = lean_array_fget(x_24, x_25);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_25, x_36);
lean_dec(x_25);
lean_ctor_set(x_19, 1, x_37);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_23);
lean_dec(x_20);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_21);
lean_ctor_set(x_50, 1, x_22);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_19);
lean_ctor_set(x_51, 1, x_50);
x_10 = x_51;
x_11 = x_9;
goto block_15;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_35, 0);
lean_inc(x_52);
lean_dec(x_35);
x_53 = lean_array_uget(x_1, x_3);
x_54 = lean_unbox(x_52);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_55 = l_Lean_Meta_mkEqRefl(x_53, x_5, x_6, x_7, x_8, x_9);
x_38 = x_55;
goto block_49;
}
else
{
lean_object* x_56; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_56 = l_Lean_Meta_mkHEqRefl(x_53, x_5, x_6, x_7, x_8, x_9);
x_38 = x_56;
goto block_49;
}
}
block_49:
{
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = lean_array_push(x_22, x_39);
x_42 = lean_nat_add(x_21, x_36);
lean_dec(x_21);
if (lean_is_scalar(x_23)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_23;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
if (lean_is_scalar(x_20)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_20;
}
lean_ctor_set(x_44, 0, x_19);
lean_ctor_set(x_44, 1, x_43);
x_10 = x_44;
x_11 = x_40;
goto block_15;
}
else
{
uint8_t x_45; 
lean_dec_ref(x_19);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 0);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_19);
x_57 = lean_array_fget(x_24, x_25);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_25, x_58);
lean_dec(x_25);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_24);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_26);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_23);
lean_dec(x_20);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_21);
lean_ctor_set(x_73, 1, x_22);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_60);
lean_ctor_set(x_74, 1, x_73);
x_10 = x_74;
x_11 = x_9;
goto block_15;
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_57, 0);
lean_inc(x_75);
lean_dec(x_57);
x_76 = lean_array_uget(x_1, x_3);
x_77 = lean_unbox(x_75);
lean_dec(x_75);
if (x_77 == 0)
{
lean_object* x_78; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_78 = l_Lean_Meta_mkEqRefl(x_76, x_5, x_6, x_7, x_8, x_9);
x_61 = x_78;
goto block_72;
}
else
{
lean_object* x_79; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_79 = l_Lean_Meta_mkHEqRefl(x_76, x_5, x_6, x_7, x_8, x_9);
x_61 = x_79;
goto block_72;
}
}
block_72:
{
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = lean_array_push(x_22, x_62);
x_65 = lean_nat_add(x_21, x_58);
lean_dec(x_21);
if (lean_is_scalar(x_23)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_23;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
if (lean_is_scalar(x_20)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_20;
}
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
x_10 = x_67;
x_11 = x_63;
goto block_15;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec_ref(x_60);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_61, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_70 = x_61;
} else {
 lean_dec_ref(x_61);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
}
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_4 = x_10;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_nat_add(x_6, x_1);
lean_dec(x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_14 = l_Lean_Meta_instantiateLambda(x_1, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_17 = lean_apply_8(x_3, x_4, x_5, x_15, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l_Array_append___redArg(x_2, x_6);
x_21 = 1;
x_22 = l_Lean_Meta_mkLambdaFVars(x_20, x_18, x_7, x_8, x_7, x_8, x_21, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_22;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
return x_17;
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_1);
x_15 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_box(x_3);
x_19 = lean_box(x_7);
lean_inc_ref(x_4);
x_20 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__0___boxed), 13, 8);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_4);
lean_closure_set(x_20, 2, x_5);
lean_closure_set(x_20, 3, x_6);
lean_closure_set(x_20, 4, x_9);
lean_closure_set(x_20, 5, x_8);
lean_closure_set(x_20, 6, x_18);
lean_closure_set(x_20, 7, x_19);
x_21 = l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10___redArg(x_4, x_16, x_20, x_10, x_11, x_12, x_13, x_17);
lean_dec(x_16);
lean_dec_ref(x_4);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_box(x_3);
x_16 = lean_box(x_6);
x_17 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__1___boxed), 14, 7);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_15);
lean_closure_set(x_17, 3, x_8);
lean_closure_set(x_17, 4, x_4);
lean_closure_set(x_17, 5, x_5);
lean_closure_set(x_17, 6, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_7);
x_19 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_9, x_18, x_17, x_3, x_3, x_10, x_11, x_12, x_13, x_14);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_15, 1);
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_16, 2);
lean_inc(x_28);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_13);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_32 = lean_ctor_get(x_16, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_16, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_16, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_21, 2);
lean_inc(x_37);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_27, x_38);
lean_inc_ref(x_26);
lean_ctor_set(x_16, 1, x_39);
x_40 = lean_nat_dec_lt(x_36, x_37);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_7);
lean_ctor_set(x_41, 1, x_13);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_43 = lean_ctor_get(x_21, 2);
lean_dec(x_43);
x_44 = lean_ctor_get(x_21, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_21, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_18, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_18, 2);
lean_inc(x_48);
x_49 = lean_nat_add(x_36, x_38);
lean_inc_ref(x_35);
lean_ctor_set(x_21, 1, x_49);
x_50 = lean_nat_dec_lt(x_47, x_48);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_7);
lean_ctor_set(x_51, 1, x_13);
return x_51;
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_18);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_53 = lean_ctor_get(x_18, 2);
lean_dec(x_53);
x_54 = lean_ctor_get(x_18, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_18, 0);
lean_dec(x_55);
x_56 = lean_array_fget(x_26, x_27);
lean_dec(x_27);
lean_dec_ref(x_26);
x_57 = lean_array_fget(x_35, x_36);
lean_dec(x_36);
lean_dec_ref(x_35);
x_58 = lean_array_fget(x_46, x_47);
x_59 = lean_box(x_2);
x_60 = lean_box(x_4);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_61 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2___boxed), 14, 7);
lean_closure_set(x_61, 0, x_58);
lean_closure_set(x_61, 1, x_1);
lean_closure_set(x_61, 2, x_59);
lean_closure_set(x_61, 3, x_3);
lean_closure_set(x_61, 4, x_8);
lean_closure_set(x_61, 5, x_60);
lean_closure_set(x_61, 6, x_5);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_57);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_63 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_56, x_62, x_61, x_2, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
x_67 = lean_nat_add(x_47, x_38);
lean_dec(x_47);
lean_ctor_set(x_18, 1, x_67);
x_68 = lean_array_push(x_24, x_65);
lean_ctor_set(x_15, 1, x_68);
x_69 = lean_nat_add(x_8, x_38);
lean_dec(x_8);
x_70 = lean_nat_dec_lt(x_69, x_6);
if (x_70 == 0)
{
lean_dec(x_69);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_63, 0, x_7);
return x_63;
}
else
{
lean_free_object(x_63);
x_8 = x_69;
x_13 = x_66;
goto _start;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_72 = lean_ctor_get(x_63, 0);
x_73 = lean_ctor_get(x_63, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_63);
x_74 = lean_nat_add(x_47, x_38);
lean_dec(x_47);
lean_ctor_set(x_18, 1, x_74);
x_75 = lean_array_push(x_24, x_72);
lean_ctor_set(x_15, 1, x_75);
x_76 = lean_nat_add(x_8, x_38);
lean_dec(x_8);
x_77 = lean_nat_dec_lt(x_76, x_6);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_76);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_7);
lean_ctor_set(x_78, 1, x_73);
return x_78;
}
else
{
x_8 = x_76;
x_13 = x_73;
goto _start;
}
}
}
else
{
uint8_t x_80; 
lean_free_object(x_18);
lean_dec_ref(x_21);
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_16);
lean_free_object(x_15);
lean_dec(x_24);
lean_free_object(x_14);
lean_free_object(x_7);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_63);
if (x_80 == 0)
{
return x_63;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_63, 0);
x_82 = lean_ctor_get(x_63, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_63);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_18);
x_84 = lean_array_fget(x_26, x_27);
lean_dec(x_27);
lean_dec_ref(x_26);
x_85 = lean_array_fget(x_35, x_36);
lean_dec(x_36);
lean_dec_ref(x_35);
x_86 = lean_array_fget(x_46, x_47);
x_87 = lean_box(x_2);
x_88 = lean_box(x_4);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_89 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2___boxed), 14, 7);
lean_closure_set(x_89, 0, x_86);
lean_closure_set(x_89, 1, x_1);
lean_closure_set(x_89, 2, x_87);
lean_closure_set(x_89, 3, x_3);
lean_closure_set(x_89, 4, x_8);
lean_closure_set(x_89, 5, x_88);
lean_closure_set(x_89, 6, x_5);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_85);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_91 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_84, x_90, x_89, x_2, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
x_95 = lean_nat_add(x_47, x_38);
lean_dec(x_47);
x_96 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_96, 0, x_46);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_48);
x_97 = lean_array_push(x_24, x_92);
lean_ctor_set(x_15, 1, x_97);
lean_ctor_set(x_7, 0, x_96);
x_98 = lean_nat_add(x_8, x_38);
lean_dec(x_8);
x_99 = lean_nat_dec_lt(x_98, x_6);
if (x_99 == 0)
{
lean_object* x_100; 
lean_dec(x_98);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_94)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_94;
}
lean_ctor_set(x_100, 0, x_7);
lean_ctor_set(x_100, 1, x_93);
return x_100;
}
else
{
lean_dec(x_94);
x_8 = x_98;
x_13 = x_93;
goto _start;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec_ref(x_21);
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_16);
lean_free_object(x_15);
lean_dec(x_24);
lean_free_object(x_14);
lean_free_object(x_7);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_102 = lean_ctor_get(x_91, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_91, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_104 = x_91;
} else {
 lean_dec_ref(x_91);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_dec(x_21);
x_106 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_18, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_18, 2);
lean_inc(x_108);
x_109 = lean_nat_add(x_36, x_38);
lean_inc_ref(x_35);
x_110 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_110, 0, x_35);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_37);
x_111 = lean_nat_dec_lt(x_107, x_108);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_14, 0, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_7);
lean_ctor_set(x_112, 1, x_13);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_113 = x_18;
} else {
 lean_dec_ref(x_18);
 x_113 = lean_box(0);
}
x_114 = lean_array_fget(x_26, x_27);
lean_dec(x_27);
lean_dec_ref(x_26);
x_115 = lean_array_fget(x_35, x_36);
lean_dec(x_36);
lean_dec_ref(x_35);
x_116 = lean_array_fget(x_106, x_107);
x_117 = lean_box(x_2);
x_118 = lean_box(x_4);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_119 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2___boxed), 14, 7);
lean_closure_set(x_119, 0, x_116);
lean_closure_set(x_119, 1, x_1);
lean_closure_set(x_119, 2, x_117);
lean_closure_set(x_119, 3, x_3);
lean_closure_set(x_119, 4, x_8);
lean_closure_set(x_119, 5, x_118);
lean_closure_set(x_119, 6, x_5);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_115);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_121 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_114, x_120, x_119, x_2, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
x_125 = lean_nat_add(x_107, x_38);
lean_dec(x_107);
if (lean_is_scalar(x_113)) {
 x_126 = lean_alloc_ctor(0, 3, 0);
} else {
 x_126 = x_113;
}
lean_ctor_set(x_126, 0, x_106);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_126, 2, x_108);
x_127 = lean_array_push(x_24, x_122);
lean_ctor_set(x_15, 1, x_127);
lean_ctor_set(x_14, 0, x_110);
lean_ctor_set(x_7, 0, x_126);
x_128 = lean_nat_add(x_8, x_38);
lean_dec(x_8);
x_129 = lean_nat_dec_lt(x_128, x_6);
if (x_129 == 0)
{
lean_object* x_130; 
lean_dec(x_128);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_124)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_124;
}
lean_ctor_set(x_130, 0, x_7);
lean_ctor_set(x_130, 1, x_123);
return x_130;
}
else
{
lean_dec(x_124);
x_8 = x_128;
x_13 = x_123;
goto _start;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_113);
lean_dec_ref(x_110);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_16);
lean_free_object(x_15);
lean_dec(x_24);
lean_free_object(x_14);
lean_free_object(x_7);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_132 = lean_ctor_get(x_121, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_121, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_134 = x_121;
} else {
 lean_dec_ref(x_121);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_dec(x_16);
x_136 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_21, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_21, 2);
lean_inc(x_138);
x_139 = lean_unsigned_to_nat(1u);
x_140 = lean_nat_add(x_27, x_139);
lean_inc_ref(x_26);
x_141 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_141, 0, x_26);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_141, 2, x_28);
x_142 = lean_nat_dec_lt(x_137, x_138);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_15, 0, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_7);
lean_ctor_set(x_143, 1, x_13);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_144 = x_21;
} else {
 lean_dec_ref(x_21);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_145);
x_146 = lean_ctor_get(x_18, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_18, 2);
lean_inc(x_147);
x_148 = lean_nat_add(x_137, x_139);
lean_inc_ref(x_136);
if (lean_is_scalar(x_144)) {
 x_149 = lean_alloc_ctor(0, 3, 0);
} else {
 x_149 = x_144;
}
lean_ctor_set(x_149, 0, x_136);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set(x_149, 2, x_138);
x_150 = lean_nat_dec_lt(x_146, x_147);
if (x_150 == 0)
{
lean_object* x_151; 
lean_dec(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_15, 0, x_141);
lean_ctor_set(x_14, 0, x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_7);
lean_ctor_set(x_151, 1, x_13);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_152 = x_18;
} else {
 lean_dec_ref(x_18);
 x_152 = lean_box(0);
}
x_153 = lean_array_fget(x_26, x_27);
lean_dec(x_27);
lean_dec_ref(x_26);
x_154 = lean_array_fget(x_136, x_137);
lean_dec(x_137);
lean_dec_ref(x_136);
x_155 = lean_array_fget(x_145, x_146);
x_156 = lean_box(x_2);
x_157 = lean_box(x_4);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_158 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2___boxed), 14, 7);
lean_closure_set(x_158, 0, x_155);
lean_closure_set(x_158, 1, x_1);
lean_closure_set(x_158, 2, x_156);
lean_closure_set(x_158, 3, x_3);
lean_closure_set(x_158, 4, x_8);
lean_closure_set(x_158, 5, x_157);
lean_closure_set(x_158, 6, x_5);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_154);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_160 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_153, x_159, x_158, x_2, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_163 = x_160;
} else {
 lean_dec_ref(x_160);
 x_163 = lean_box(0);
}
x_164 = lean_nat_add(x_146, x_139);
lean_dec(x_146);
if (lean_is_scalar(x_152)) {
 x_165 = lean_alloc_ctor(0, 3, 0);
} else {
 x_165 = x_152;
}
lean_ctor_set(x_165, 0, x_145);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_165, 2, x_147);
x_166 = lean_array_push(x_24, x_161);
lean_ctor_set(x_15, 1, x_166);
lean_ctor_set(x_15, 0, x_141);
lean_ctor_set(x_14, 0, x_149);
lean_ctor_set(x_7, 0, x_165);
x_167 = lean_nat_add(x_8, x_139);
lean_dec(x_8);
x_168 = lean_nat_dec_lt(x_167, x_6);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_167);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_163)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_163;
}
lean_ctor_set(x_169, 0, x_7);
lean_ctor_set(x_169, 1, x_162);
return x_169;
}
else
{
lean_dec(x_163);
x_8 = x_167;
x_13 = x_162;
goto _start;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_152);
lean_dec_ref(x_149);
lean_dec(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec_ref(x_141);
lean_free_object(x_15);
lean_dec(x_24);
lean_free_object(x_14);
lean_free_object(x_7);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_171 = lean_ctor_get(x_160, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_160, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_173 = x_160;
} else {
 lean_dec_ref(x_160);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_175 = lean_ctor_get(x_15, 1);
lean_inc(x_175);
lean_dec(x_15);
x_176 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_176);
x_177 = lean_ctor_get(x_16, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_16, 2);
lean_inc(x_178);
x_179 = lean_nat_dec_lt(x_177, x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_178);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_16);
lean_ctor_set(x_180, 1, x_175);
lean_ctor_set(x_14, 1, x_180);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_7);
lean_ctor_set(x_181, 1, x_13);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 x_182 = x_16;
} else {
 lean_dec_ref(x_16);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_183);
x_184 = lean_ctor_get(x_21, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_21, 2);
lean_inc(x_185);
x_186 = lean_unsigned_to_nat(1u);
x_187 = lean_nat_add(x_177, x_186);
lean_inc_ref(x_176);
if (lean_is_scalar(x_182)) {
 x_188 = lean_alloc_ctor(0, 3, 0);
} else {
 x_188 = x_182;
}
lean_ctor_set(x_188, 0, x_176);
lean_ctor_set(x_188, 1, x_187);
lean_ctor_set(x_188, 2, x_178);
x_189 = lean_nat_dec_lt(x_184, x_185);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_185);
lean_dec(x_184);
lean_dec_ref(x_183);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_175);
lean_ctor_set(x_14, 1, x_190);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_7);
lean_ctor_set(x_191, 1, x_13);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_192 = x_21;
} else {
 lean_dec_ref(x_21);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_193);
x_194 = lean_ctor_get(x_18, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_18, 2);
lean_inc(x_195);
x_196 = lean_nat_add(x_184, x_186);
lean_inc_ref(x_183);
if (lean_is_scalar(x_192)) {
 x_197 = lean_alloc_ctor(0, 3, 0);
} else {
 x_197 = x_192;
}
lean_ctor_set(x_197, 0, x_183);
lean_ctor_set(x_197, 1, x_196);
lean_ctor_set(x_197, 2, x_185);
x_198 = lean_nat_dec_lt(x_194, x_195);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
lean_dec(x_184);
lean_dec_ref(x_183);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_188);
lean_ctor_set(x_199, 1, x_175);
lean_ctor_set(x_14, 1, x_199);
lean_ctor_set(x_14, 0, x_197);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_7);
lean_ctor_set(x_200, 1, x_13);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_201 = x_18;
} else {
 lean_dec_ref(x_18);
 x_201 = lean_box(0);
}
x_202 = lean_array_fget(x_176, x_177);
lean_dec(x_177);
lean_dec_ref(x_176);
x_203 = lean_array_fget(x_183, x_184);
lean_dec(x_184);
lean_dec_ref(x_183);
x_204 = lean_array_fget(x_193, x_194);
x_205 = lean_box(x_2);
x_206 = lean_box(x_4);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_207 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2___boxed), 14, 7);
lean_closure_set(x_207, 0, x_204);
lean_closure_set(x_207, 1, x_1);
lean_closure_set(x_207, 2, x_205);
lean_closure_set(x_207, 3, x_3);
lean_closure_set(x_207, 4, x_8);
lean_closure_set(x_207, 5, x_206);
lean_closure_set(x_207, 6, x_5);
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_203);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_209 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_202, x_208, x_207, x_2, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_212 = x_209;
} else {
 lean_dec_ref(x_209);
 x_212 = lean_box(0);
}
x_213 = lean_nat_add(x_194, x_186);
lean_dec(x_194);
if (lean_is_scalar(x_201)) {
 x_214 = lean_alloc_ctor(0, 3, 0);
} else {
 x_214 = x_201;
}
lean_ctor_set(x_214, 0, x_193);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set(x_214, 2, x_195);
x_215 = lean_array_push(x_175, x_210);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_188);
lean_ctor_set(x_216, 1, x_215);
lean_ctor_set(x_14, 1, x_216);
lean_ctor_set(x_14, 0, x_197);
lean_ctor_set(x_7, 0, x_214);
x_217 = lean_nat_add(x_8, x_186);
lean_dec(x_8);
x_218 = lean_nat_dec_lt(x_217, x_6);
if (x_218 == 0)
{
lean_object* x_219; 
lean_dec(x_217);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_212)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_212;
}
lean_ctor_set(x_219, 0, x_7);
lean_ctor_set(x_219, 1, x_211);
return x_219;
}
else
{
lean_dec(x_212);
x_8 = x_217;
x_13 = x_211;
goto _start;
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_201);
lean_dec_ref(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec_ref(x_193);
lean_dec_ref(x_188);
lean_dec(x_175);
lean_free_object(x_14);
lean_free_object(x_7);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_221 = lean_ctor_get(x_209, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_209, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_223 = x_209;
} else {
 lean_dec_ref(x_209);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
}
}
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_225 = lean_ctor_get(x_14, 0);
lean_inc(x_225);
lean_dec(x_14);
x_226 = lean_ctor_get(x_15, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_227 = x_15;
} else {
 lean_dec_ref(x_15);
 x_227 = lean_box(0);
}
x_228 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_228);
x_229 = lean_ctor_get(x_16, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_16, 2);
lean_inc(x_230);
x_231 = lean_nat_dec_lt(x_229, x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_230);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_227)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_227;
}
lean_ctor_set(x_232, 0, x_16);
lean_ctor_set(x_232, 1, x_226);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_225);
lean_ctor_set(x_233, 1, x_232);
lean_ctor_set(x_7, 1, x_233);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_7);
lean_ctor_set(x_234, 1, x_13);
return x_234;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 x_235 = x_16;
} else {
 lean_dec_ref(x_16);
 x_235 = lean_box(0);
}
x_236 = lean_ctor_get(x_225, 0);
lean_inc_ref(x_236);
x_237 = lean_ctor_get(x_225, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_225, 2);
lean_inc(x_238);
x_239 = lean_unsigned_to_nat(1u);
x_240 = lean_nat_add(x_229, x_239);
lean_inc_ref(x_228);
if (lean_is_scalar(x_235)) {
 x_241 = lean_alloc_ctor(0, 3, 0);
} else {
 x_241 = x_235;
}
lean_ctor_set(x_241, 0, x_228);
lean_ctor_set(x_241, 1, x_240);
lean_ctor_set(x_241, 2, x_230);
x_242 = lean_nat_dec_lt(x_237, x_238);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_227)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_227;
}
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_226);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_225);
lean_ctor_set(x_244, 1, x_243);
lean_ctor_set(x_7, 1, x_244);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_7);
lean_ctor_set(x_245, 1, x_13);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 lean_ctor_release(x_225, 2);
 x_246 = x_225;
} else {
 lean_dec_ref(x_225);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_247);
x_248 = lean_ctor_get(x_18, 1);
lean_inc(x_248);
x_249 = lean_ctor_get(x_18, 2);
lean_inc(x_249);
x_250 = lean_nat_add(x_237, x_239);
lean_inc_ref(x_236);
if (lean_is_scalar(x_246)) {
 x_251 = lean_alloc_ctor(0, 3, 0);
} else {
 x_251 = x_246;
}
lean_ctor_set(x_251, 0, x_236);
lean_ctor_set(x_251, 1, x_250);
lean_ctor_set(x_251, 2, x_238);
x_252 = lean_nat_dec_lt(x_248, x_249);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_249);
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_227)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_227;
}
lean_ctor_set(x_253, 0, x_241);
lean_ctor_set(x_253, 1, x_226);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_253);
lean_ctor_set(x_7, 1, x_254);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_7);
lean_ctor_set(x_255, 1, x_13);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_256 = x_18;
} else {
 lean_dec_ref(x_18);
 x_256 = lean_box(0);
}
x_257 = lean_array_fget(x_228, x_229);
lean_dec(x_229);
lean_dec_ref(x_228);
x_258 = lean_array_fget(x_236, x_237);
lean_dec(x_237);
lean_dec_ref(x_236);
x_259 = lean_array_fget(x_247, x_248);
x_260 = lean_box(x_2);
x_261 = lean_box(x_4);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_262 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2___boxed), 14, 7);
lean_closure_set(x_262, 0, x_259);
lean_closure_set(x_262, 1, x_1);
lean_closure_set(x_262, 2, x_260);
lean_closure_set(x_262, 3, x_3);
lean_closure_set(x_262, 4, x_8);
lean_closure_set(x_262, 5, x_261);
lean_closure_set(x_262, 6, x_5);
x_263 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_263, 0, x_258);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_264 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_257, x_263, x_262, x_2, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_267 = x_264;
} else {
 lean_dec_ref(x_264);
 x_267 = lean_box(0);
}
x_268 = lean_nat_add(x_248, x_239);
lean_dec(x_248);
if (lean_is_scalar(x_256)) {
 x_269 = lean_alloc_ctor(0, 3, 0);
} else {
 x_269 = x_256;
}
lean_ctor_set(x_269, 0, x_247);
lean_ctor_set(x_269, 1, x_268);
lean_ctor_set(x_269, 2, x_249);
x_270 = lean_array_push(x_226, x_265);
if (lean_is_scalar(x_227)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_227;
}
lean_ctor_set(x_271, 0, x_241);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_251);
lean_ctor_set(x_272, 1, x_271);
lean_ctor_set(x_7, 1, x_272);
lean_ctor_set(x_7, 0, x_269);
x_273 = lean_nat_add(x_8, x_239);
lean_dec(x_8);
x_274 = lean_nat_dec_lt(x_273, x_6);
if (x_274 == 0)
{
lean_object* x_275; 
lean_dec(x_273);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_267)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_267;
}
lean_ctor_set(x_275, 0, x_7);
lean_ctor_set(x_275, 1, x_266);
return x_275;
}
else
{
lean_dec(x_267);
x_8 = x_273;
x_13 = x_266;
goto _start;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_256);
lean_dec_ref(x_251);
lean_dec(x_249);
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec_ref(x_241);
lean_dec(x_227);
lean_dec(x_226);
lean_free_object(x_7);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_277 = lean_ctor_get(x_264, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_264, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_279 = x_264;
} else {
 lean_dec_ref(x_264);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
}
}
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_281 = lean_ctor_get(x_7, 0);
lean_inc(x_281);
lean_dec(x_7);
x_282 = lean_ctor_get(x_14, 0);
lean_inc(x_282);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_283 = x_14;
} else {
 lean_dec_ref(x_14);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_15, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_285 = x_15;
} else {
 lean_dec_ref(x_15);
 x_285 = lean_box(0);
}
x_286 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_286);
x_287 = lean_ctor_get(x_16, 1);
lean_inc(x_287);
x_288 = lean_ctor_get(x_16, 2);
lean_inc(x_288);
x_289 = lean_nat_dec_lt(x_287, x_288);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_288);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_285)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_285;
}
lean_ctor_set(x_290, 0, x_16);
lean_ctor_set(x_290, 1, x_284);
if (lean_is_scalar(x_283)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_283;
}
lean_ctor_set(x_291, 0, x_282);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_281);
lean_ctor_set(x_292, 1, x_291);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_13);
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 x_294 = x_16;
} else {
 lean_dec_ref(x_16);
 x_294 = lean_box(0);
}
x_295 = lean_ctor_get(x_282, 0);
lean_inc_ref(x_295);
x_296 = lean_ctor_get(x_282, 1);
lean_inc(x_296);
x_297 = lean_ctor_get(x_282, 2);
lean_inc(x_297);
x_298 = lean_unsigned_to_nat(1u);
x_299 = lean_nat_add(x_287, x_298);
lean_inc_ref(x_286);
if (lean_is_scalar(x_294)) {
 x_300 = lean_alloc_ctor(0, 3, 0);
} else {
 x_300 = x_294;
}
lean_ctor_set(x_300, 0, x_286);
lean_ctor_set(x_300, 1, x_299);
lean_ctor_set(x_300, 2, x_288);
x_301 = lean_nat_dec_lt(x_296, x_297);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_297);
lean_dec(x_296);
lean_dec_ref(x_295);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_285)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_285;
}
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_284);
if (lean_is_scalar(x_283)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_283;
}
lean_ctor_set(x_303, 0, x_282);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_281);
lean_ctor_set(x_304, 1, x_303);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_13);
return x_305;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 lean_ctor_release(x_282, 2);
 x_306 = x_282;
} else {
 lean_dec_ref(x_282);
 x_306 = lean_box(0);
}
x_307 = lean_ctor_get(x_281, 0);
lean_inc_ref(x_307);
x_308 = lean_ctor_get(x_281, 1);
lean_inc(x_308);
x_309 = lean_ctor_get(x_281, 2);
lean_inc(x_309);
x_310 = lean_nat_add(x_296, x_298);
lean_inc_ref(x_295);
if (lean_is_scalar(x_306)) {
 x_311 = lean_alloc_ctor(0, 3, 0);
} else {
 x_311 = x_306;
}
lean_ctor_set(x_311, 0, x_295);
lean_ctor_set(x_311, 1, x_310);
lean_ctor_set(x_311, 2, x_297);
x_312 = lean_nat_dec_lt(x_308, x_309);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec(x_296);
lean_dec_ref(x_295);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_285)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_285;
}
lean_ctor_set(x_313, 0, x_300);
lean_ctor_set(x_313, 1, x_284);
if (lean_is_scalar(x_283)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_283;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_313);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_281);
lean_ctor_set(x_315, 1, x_314);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_13);
return x_316;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 lean_ctor_release(x_281, 2);
 x_317 = x_281;
} else {
 lean_dec_ref(x_281);
 x_317 = lean_box(0);
}
x_318 = lean_array_fget(x_286, x_287);
lean_dec(x_287);
lean_dec_ref(x_286);
x_319 = lean_array_fget(x_295, x_296);
lean_dec(x_296);
lean_dec_ref(x_295);
x_320 = lean_array_fget(x_307, x_308);
x_321 = lean_box(x_2);
x_322 = lean_box(x_4);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_323 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2___boxed), 14, 7);
lean_closure_set(x_323, 0, x_320);
lean_closure_set(x_323, 1, x_1);
lean_closure_set(x_323, 2, x_321);
lean_closure_set(x_323, 3, x_3);
lean_closure_set(x_323, 4, x_8);
lean_closure_set(x_323, 5, x_322);
lean_closure_set(x_323, 6, x_5);
x_324 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_324, 0, x_319);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_325 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_318, x_324, x_323, x_2, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_328 = x_325;
} else {
 lean_dec_ref(x_325);
 x_328 = lean_box(0);
}
x_329 = lean_nat_add(x_308, x_298);
lean_dec(x_308);
if (lean_is_scalar(x_317)) {
 x_330 = lean_alloc_ctor(0, 3, 0);
} else {
 x_330 = x_317;
}
lean_ctor_set(x_330, 0, x_307);
lean_ctor_set(x_330, 1, x_329);
lean_ctor_set(x_330, 2, x_309);
x_331 = lean_array_push(x_284, x_326);
if (lean_is_scalar(x_285)) {
 x_332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_332 = x_285;
}
lean_ctor_set(x_332, 0, x_300);
lean_ctor_set(x_332, 1, x_331);
if (lean_is_scalar(x_283)) {
 x_333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_333 = x_283;
}
lean_ctor_set(x_333, 0, x_311);
lean_ctor_set(x_333, 1, x_332);
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_330);
lean_ctor_set(x_334, 1, x_333);
x_335 = lean_nat_add(x_8, x_298);
lean_dec(x_8);
x_336 = lean_nat_dec_lt(x_335, x_6);
if (x_336 == 0)
{
lean_object* x_337; 
lean_dec(x_335);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_328)) {
 x_337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_337 = x_328;
}
lean_ctor_set(x_337, 0, x_334);
lean_ctor_set(x_337, 1, x_327);
return x_337;
}
else
{
lean_dec(x_328);
x_7 = x_334;
x_8 = x_335;
x_13 = x_327;
goto _start;
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_317);
lean_dec_ref(x_311);
lean_dec(x_309);
lean_dec(x_308);
lean_dec_ref(x_307);
lean_dec_ref(x_300);
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_339 = lean_ctor_get(x_325, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_325, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_341 = x_325;
} else {
 lean_dec_ref(x_325);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(1, 2, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_339);
lean_ctor_set(x_342, 1, x_340);
return x_342;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
x_21 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg(x_1, x_2, x_3, x_4, x_5, x_10, x_12, x_13, x_16, x_17, x_18, x_19, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_7(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_10, 0, x_4);
x_11 = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_29; lean_object* x_30; 
x_29 = l_Array_append___redArg(x_8, x_5);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_30 = l_Lean_Meta_instantiateLambda(x_9, x_29, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_29);
if (lean_obj_tag(x_30) == 0)
{
x_17 = x_30;
goto block_28;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_37; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
x_37 = l_Lean_Exception_isInterrupt(x_31);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = l_Lean_Exception_isRuntime(x_31);
lean_dec(x_31);
x_33 = x_38;
goto block_36;
}
else
{
lean_dec(x_31);
x_33 = x_37;
goto block_36;
}
block_36:
{
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_30);
x_34 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2;
x_35 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_34, x_12, x_13, x_14, x_15, x_32);
x_17 = x_35;
goto block_28;
}
else
{
lean_dec(x_32);
x_17 = x_30;
goto block_28;
}
}
}
block_28:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_20 = lean_apply_8(x_1, x_2, x_11, x_18, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = l_Array_append___redArg(x_3, x_4);
x_24 = l_Array_append___redArg(x_23, x_5);
x_25 = l_Array_append___redArg(x_24, x_10);
x_26 = 1;
x_27 = l_Lean_Meta_mkLambdaFVars(x_25, x_21, x_6, x_7, x_6, x_7, x_26, x_12, x_13, x_14, x_15, x_22);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
return x_27;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_3);
return x_20;
}
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_box(x_5);
x_18 = lean_box(x_6);
x_19 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__0___boxed), 16, 9);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_4);
lean_closure_set(x_19, 4, x_10);
lean_closure_set(x_19, 5, x_17);
lean_closure_set(x_19, 6, x_18);
lean_closure_set(x_19, 7, x_7);
lean_closure_set(x_19, 8, x_8);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_9);
x_21 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_11, x_20, x_19, x_5, x_5, x_12, x_13, x_14, x_15, x_16);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_box(x_4);
x_18 = lean_box(x_5);
x_19 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__1___boxed), 16, 9);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_10);
lean_closure_set(x_19, 4, x_17);
lean_closure_set(x_19, 5, x_18);
lean_closure_set(x_19, 6, x_6);
lean_closure_set(x_19, 7, x_7);
lean_closure_set(x_19, 8, x_8);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_9);
x_21 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_11, x_20, x_19, x_4, x_4, x_12, x_13, x_14, x_15, x_16);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_17 = l_Lean_Meta_instantiateForall(x_1, x_10, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_box(x_4);
x_21 = lean_box(x_5);
lean_inc_ref(x_10);
x_22 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__2___boxed), 16, 9);
lean_closure_set(x_22, 0, x_2);
lean_closure_set(x_22, 1, x_3);
lean_closure_set(x_22, 2, x_10);
lean_closure_set(x_22, 3, x_20);
lean_closure_set(x_22, 4, x_21);
lean_closure_set(x_22, 5, x_11);
lean_closure_set(x_22, 6, x_6);
lean_closure_set(x_22, 7, x_7);
lean_closure_set(x_22, 8, x_8);
x_23 = lean_array_get_size(x_10);
lean_dec_ref(x_10);
x_24 = lean_nat_sub(x_9, x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_18, x_25, x_22, x_4, x_4, x_12, x_13, x_14, x_15, x_19);
return x_26;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_18, 1);
x_34 = lean_ctor_get(x_18, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_19, 2);
lean_inc(x_37);
x_38 = lean_nat_dec_lt(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_8);
lean_ctor_set(x_39, 1, x_14);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_19);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_41 = lean_ctor_get(x_19, 2);
lean_dec(x_41);
x_42 = lean_ctor_get(x_19, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_19, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_30, 2);
lean_inc(x_46);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_36, x_47);
lean_inc_ref(x_35);
lean_ctor_set(x_19, 1, x_48);
x_49 = lean_nat_dec_lt(x_45, x_46);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_8);
lean_ctor_set(x_50, 1, x_14);
return x_50;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_30);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_52 = lean_ctor_get(x_30, 2);
lean_dec(x_52);
x_53 = lean_ctor_get(x_30, 1);
lean_dec(x_53);
x_54 = lean_ctor_get(x_30, 0);
lean_dec(x_54);
x_55 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_27, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_27, 2);
lean_inc(x_57);
x_58 = lean_nat_add(x_45, x_47);
lean_inc_ref(x_44);
lean_ctor_set(x_30, 1, x_58);
x_59 = lean_nat_dec_lt(x_56, x_57);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_8);
lean_ctor_set(x_60, 1, x_14);
return x_60;
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_27);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_62 = lean_ctor_get(x_27, 2);
lean_dec(x_62);
x_63 = lean_ctor_get(x_27, 1);
lean_dec(x_63);
x_64 = lean_ctor_get(x_27, 0);
lean_dec(x_64);
x_65 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_24, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_24, 2);
lean_inc(x_67);
x_68 = lean_nat_add(x_56, x_47);
lean_inc_ref(x_55);
lean_ctor_set(x_27, 1, x_68);
x_69 = lean_nat_dec_lt(x_66, x_67);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_8);
lean_ctor_set(x_70, 1, x_14);
return x_70;
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_24);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_72 = lean_ctor_get(x_24, 2);
lean_dec(x_72);
x_73 = lean_ctor_get(x_24, 1);
lean_dec(x_73);
x_74 = lean_ctor_get(x_24, 0);
lean_dec(x_74);
x_75 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_21, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_21, 2);
lean_inc(x_77);
x_78 = lean_nat_add(x_66, x_47);
lean_inc_ref(x_65);
lean_ctor_set(x_24, 1, x_78);
x_79 = lean_nat_dec_lt(x_76, x_77);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_8);
lean_ctor_set(x_80, 1, x_14);
return x_80;
}
else
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_21);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_82 = lean_ctor_get(x_21, 2);
lean_dec(x_82);
x_83 = lean_ctor_get(x_21, 1);
lean_dec(x_83);
x_84 = lean_ctor_get(x_21, 0);
lean_dec(x_84);
x_85 = lean_array_fget(x_35, x_36);
lean_dec(x_36);
lean_dec_ref(x_35);
x_86 = lean_array_fget(x_44, x_45);
lean_dec(x_45);
lean_dec_ref(x_44);
x_87 = lean_array_fget(x_55, x_56);
lean_dec(x_56);
lean_dec_ref(x_55);
x_88 = lean_array_fget(x_65, x_66);
lean_dec(x_66);
lean_dec_ref(x_65);
x_89 = lean_array_fget(x_75, x_76);
x_90 = lean_box(x_2);
x_91 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_92 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_92, 0, x_85);
lean_closure_set(x_92, 1, x_1);
lean_closure_set(x_92, 2, x_9);
lean_closure_set(x_92, 3, x_90);
lean_closure_set(x_92, 4, x_91);
lean_closure_set(x_92, 5, x_89);
lean_closure_set(x_92, 6, x_4);
lean_closure_set(x_92, 7, x_5);
lean_closure_set(x_92, 8, x_87);
x_93 = lean_nat_sub(x_88, x_5);
lean_dec(x_88);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_6);
x_94 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg(x_86, x_93, x_6, x_92, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
x_98 = lean_nat_add(x_76, x_47);
lean_dec(x_76);
lean_ctor_set(x_21, 1, x_98);
x_99 = lean_array_push(x_33, x_96);
lean_ctor_set(x_18, 1, x_99);
x_100 = lean_nat_add(x_9, x_47);
lean_dec(x_9);
x_101 = lean_nat_dec_lt(x_100, x_7);
if (x_101 == 0)
{
lean_dec(x_100);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_94, 0, x_8);
return x_94;
}
else
{
lean_free_object(x_94);
x_9 = x_100;
x_14 = x_97;
goto _start;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_103 = lean_ctor_get(x_94, 0);
x_104 = lean_ctor_get(x_94, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_94);
x_105 = lean_nat_add(x_76, x_47);
lean_dec(x_76);
lean_ctor_set(x_21, 1, x_105);
x_106 = lean_array_push(x_33, x_103);
lean_ctor_set(x_18, 1, x_106);
x_107 = lean_nat_add(x_9, x_47);
lean_dec(x_9);
x_108 = lean_nat_dec_lt(x_107, x_7);
if (x_108 == 0)
{
lean_object* x_109; 
lean_dec(x_107);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_8);
lean_ctor_set(x_109, 1, x_104);
return x_109;
}
else
{
x_9 = x_107;
x_14 = x_104;
goto _start;
}
}
}
else
{
uint8_t x_111; 
lean_free_object(x_21);
lean_dec_ref(x_24);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec_ref(x_27);
lean_dec_ref(x_30);
lean_dec_ref(x_19);
lean_free_object(x_18);
lean_dec(x_33);
lean_free_object(x_17);
lean_free_object(x_16);
lean_free_object(x_15);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_94);
if (x_111 == 0)
{
return x_94;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_94, 0);
x_113 = lean_ctor_get(x_94, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_94);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_21);
x_115 = lean_array_fget(x_35, x_36);
lean_dec(x_36);
lean_dec_ref(x_35);
x_116 = lean_array_fget(x_44, x_45);
lean_dec(x_45);
lean_dec_ref(x_44);
x_117 = lean_array_fget(x_55, x_56);
lean_dec(x_56);
lean_dec_ref(x_55);
x_118 = lean_array_fget(x_65, x_66);
lean_dec(x_66);
lean_dec_ref(x_65);
x_119 = lean_array_fget(x_75, x_76);
x_120 = lean_box(x_2);
x_121 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_122 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_122, 0, x_115);
lean_closure_set(x_122, 1, x_1);
lean_closure_set(x_122, 2, x_9);
lean_closure_set(x_122, 3, x_120);
lean_closure_set(x_122, 4, x_121);
lean_closure_set(x_122, 5, x_119);
lean_closure_set(x_122, 6, x_4);
lean_closure_set(x_122, 7, x_5);
lean_closure_set(x_122, 8, x_117);
x_123 = lean_nat_sub(x_118, x_5);
lean_dec(x_118);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_6);
x_124 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg(x_116, x_123, x_6, x_122, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = lean_nat_add(x_76, x_47);
lean_dec(x_76);
x_129 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_129, 0, x_75);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_77);
x_130 = lean_array_push(x_33, x_125);
lean_ctor_set(x_18, 1, x_130);
lean_ctor_set(x_8, 0, x_129);
x_131 = lean_nat_add(x_9, x_47);
lean_dec(x_9);
x_132 = lean_nat_dec_lt(x_131, x_7);
if (x_132 == 0)
{
lean_object* x_133; 
lean_dec(x_131);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_127)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_127;
}
lean_ctor_set(x_133, 0, x_8);
lean_ctor_set(x_133, 1, x_126);
return x_133;
}
else
{
lean_dec(x_127);
x_9 = x_131;
x_14 = x_126;
goto _start;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec_ref(x_24);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec_ref(x_27);
lean_dec_ref(x_30);
lean_dec_ref(x_19);
lean_free_object(x_18);
lean_dec(x_33);
lean_free_object(x_17);
lean_free_object(x_16);
lean_free_object(x_15);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_135 = lean_ctor_get(x_124, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_124, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_137 = x_124;
} else {
 lean_dec_ref(x_124);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_dec(x_24);
x_139 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_139);
x_140 = lean_ctor_get(x_21, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_21, 2);
lean_inc(x_141);
x_142 = lean_nat_add(x_66, x_47);
lean_inc_ref(x_65);
x_143 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_143, 0, x_65);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_143, 2, x_67);
x_144 = lean_nat_dec_lt(x_140, x_141);
if (x_144 == 0)
{
lean_object* x_145; 
lean_dec(x_141);
lean_dec(x_140);
lean_dec_ref(x_139);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_15, 0, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_8);
lean_ctor_set(x_145, 1, x_14);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_146 = x_21;
} else {
 lean_dec_ref(x_21);
 x_146 = lean_box(0);
}
x_147 = lean_array_fget(x_35, x_36);
lean_dec(x_36);
lean_dec_ref(x_35);
x_148 = lean_array_fget(x_44, x_45);
lean_dec(x_45);
lean_dec_ref(x_44);
x_149 = lean_array_fget(x_55, x_56);
lean_dec(x_56);
lean_dec_ref(x_55);
x_150 = lean_array_fget(x_65, x_66);
lean_dec(x_66);
lean_dec_ref(x_65);
x_151 = lean_array_fget(x_139, x_140);
x_152 = lean_box(x_2);
x_153 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_154 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_154, 0, x_147);
lean_closure_set(x_154, 1, x_1);
lean_closure_set(x_154, 2, x_9);
lean_closure_set(x_154, 3, x_152);
lean_closure_set(x_154, 4, x_153);
lean_closure_set(x_154, 5, x_151);
lean_closure_set(x_154, 6, x_4);
lean_closure_set(x_154, 7, x_5);
lean_closure_set(x_154, 8, x_149);
x_155 = lean_nat_sub(x_150, x_5);
lean_dec(x_150);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_6);
x_156 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg(x_148, x_155, x_6, x_154, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
x_160 = lean_nat_add(x_140, x_47);
lean_dec(x_140);
if (lean_is_scalar(x_146)) {
 x_161 = lean_alloc_ctor(0, 3, 0);
} else {
 x_161 = x_146;
}
lean_ctor_set(x_161, 0, x_139);
lean_ctor_set(x_161, 1, x_160);
lean_ctor_set(x_161, 2, x_141);
x_162 = lean_array_push(x_33, x_157);
lean_ctor_set(x_18, 1, x_162);
lean_ctor_set(x_15, 0, x_143);
lean_ctor_set(x_8, 0, x_161);
x_163 = lean_nat_add(x_9, x_47);
lean_dec(x_9);
x_164 = lean_nat_dec_lt(x_163, x_7);
if (x_164 == 0)
{
lean_object* x_165; 
lean_dec(x_163);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_159)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_159;
}
lean_ctor_set(x_165, 0, x_8);
lean_ctor_set(x_165, 1, x_158);
return x_165;
}
else
{
lean_dec(x_159);
x_9 = x_163;
x_14 = x_158;
goto _start;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_146);
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec(x_140);
lean_dec_ref(x_139);
lean_dec_ref(x_27);
lean_dec_ref(x_30);
lean_dec_ref(x_19);
lean_free_object(x_18);
lean_dec(x_33);
lean_free_object(x_17);
lean_free_object(x_16);
lean_free_object(x_15);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_167 = lean_ctor_get(x_156, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_156, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_169 = x_156;
} else {
 lean_dec_ref(x_156);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
lean_dec(x_27);
x_171 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_24, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_24, 2);
lean_inc(x_173);
x_174 = lean_nat_add(x_56, x_47);
lean_inc_ref(x_55);
x_175 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_175, 0, x_55);
lean_ctor_set(x_175, 1, x_174);
lean_ctor_set(x_175, 2, x_57);
x_176 = lean_nat_dec_lt(x_172, x_173);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec(x_173);
lean_dec(x_172);
lean_dec_ref(x_171);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_16, 0, x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_8);
lean_ctor_set(x_177, 1, x_14);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 x_178 = x_24;
} else {
 lean_dec_ref(x_24);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_179);
x_180 = lean_ctor_get(x_21, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_21, 2);
lean_inc(x_181);
x_182 = lean_nat_add(x_172, x_47);
lean_inc_ref(x_171);
if (lean_is_scalar(x_178)) {
 x_183 = lean_alloc_ctor(0, 3, 0);
} else {
 x_183 = x_178;
}
lean_ctor_set(x_183, 0, x_171);
lean_ctor_set(x_183, 1, x_182);
lean_ctor_set(x_183, 2, x_173);
x_184 = lean_nat_dec_lt(x_180, x_181);
if (x_184 == 0)
{
lean_object* x_185; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec_ref(x_179);
lean_dec(x_172);
lean_dec_ref(x_171);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_16, 0, x_175);
lean_ctor_set(x_15, 0, x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_8);
lean_ctor_set(x_185, 1, x_14);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_186 = x_21;
} else {
 lean_dec_ref(x_21);
 x_186 = lean_box(0);
}
x_187 = lean_array_fget(x_35, x_36);
lean_dec(x_36);
lean_dec_ref(x_35);
x_188 = lean_array_fget(x_44, x_45);
lean_dec(x_45);
lean_dec_ref(x_44);
x_189 = lean_array_fget(x_55, x_56);
lean_dec(x_56);
lean_dec_ref(x_55);
x_190 = lean_array_fget(x_171, x_172);
lean_dec(x_172);
lean_dec_ref(x_171);
x_191 = lean_array_fget(x_179, x_180);
x_192 = lean_box(x_2);
x_193 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_194 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_194, 0, x_187);
lean_closure_set(x_194, 1, x_1);
lean_closure_set(x_194, 2, x_9);
lean_closure_set(x_194, 3, x_192);
lean_closure_set(x_194, 4, x_193);
lean_closure_set(x_194, 5, x_191);
lean_closure_set(x_194, 6, x_4);
lean_closure_set(x_194, 7, x_5);
lean_closure_set(x_194, 8, x_189);
x_195 = lean_nat_sub(x_190, x_5);
lean_dec(x_190);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_6);
x_196 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg(x_188, x_195, x_6, x_194, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_199 = x_196;
} else {
 lean_dec_ref(x_196);
 x_199 = lean_box(0);
}
x_200 = lean_nat_add(x_180, x_47);
lean_dec(x_180);
if (lean_is_scalar(x_186)) {
 x_201 = lean_alloc_ctor(0, 3, 0);
} else {
 x_201 = x_186;
}
lean_ctor_set(x_201, 0, x_179);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set(x_201, 2, x_181);
x_202 = lean_array_push(x_33, x_197);
lean_ctor_set(x_18, 1, x_202);
lean_ctor_set(x_16, 0, x_175);
lean_ctor_set(x_15, 0, x_183);
lean_ctor_set(x_8, 0, x_201);
x_203 = lean_nat_add(x_9, x_47);
lean_dec(x_9);
x_204 = lean_nat_dec_lt(x_203, x_7);
if (x_204 == 0)
{
lean_object* x_205; 
lean_dec(x_203);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_199)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_199;
}
lean_ctor_set(x_205, 0, x_8);
lean_ctor_set(x_205, 1, x_198);
return x_205;
}
else
{
lean_dec(x_199);
x_9 = x_203;
x_14 = x_198;
goto _start;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_186);
lean_dec_ref(x_183);
lean_dec(x_181);
lean_dec(x_180);
lean_dec_ref(x_179);
lean_dec_ref(x_175);
lean_dec_ref(x_30);
lean_dec_ref(x_19);
lean_free_object(x_18);
lean_dec(x_33);
lean_free_object(x_17);
lean_free_object(x_16);
lean_free_object(x_15);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_207 = lean_ctor_get(x_196, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_196, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_209 = x_196;
} else {
 lean_dec_ref(x_196);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
}
}
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
lean_dec(x_30);
x_211 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_211);
x_212 = lean_ctor_get(x_27, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_27, 2);
lean_inc(x_213);
x_214 = lean_nat_add(x_45, x_47);
lean_inc_ref(x_44);
x_215 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_215, 0, x_44);
lean_ctor_set(x_215, 1, x_214);
lean_ctor_set(x_215, 2, x_46);
x_216 = lean_nat_dec_lt(x_212, x_213);
if (x_216 == 0)
{
lean_object* x_217; 
lean_dec(x_213);
lean_dec(x_212);
lean_dec_ref(x_211);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_17, 0, x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_8);
lean_ctor_set(x_217, 1, x_14);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 x_218 = x_27;
} else {
 lean_dec_ref(x_27);
 x_218 = lean_box(0);
}
x_219 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_219);
x_220 = lean_ctor_get(x_24, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_24, 2);
lean_inc(x_221);
x_222 = lean_nat_add(x_212, x_47);
lean_inc_ref(x_211);
if (lean_is_scalar(x_218)) {
 x_223 = lean_alloc_ctor(0, 3, 0);
} else {
 x_223 = x_218;
}
lean_ctor_set(x_223, 0, x_211);
lean_ctor_set(x_223, 1, x_222);
lean_ctor_set(x_223, 2, x_213);
x_224 = lean_nat_dec_lt(x_220, x_221);
if (x_224 == 0)
{
lean_object* x_225; 
lean_dec(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_212);
lean_dec_ref(x_211);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_17, 0, x_215);
lean_ctor_set(x_16, 0, x_223);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_8);
lean_ctor_set(x_225, 1, x_14);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 x_226 = x_24;
} else {
 lean_dec_ref(x_24);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_227);
x_228 = lean_ctor_get(x_21, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_21, 2);
lean_inc(x_229);
x_230 = lean_nat_add(x_220, x_47);
lean_inc_ref(x_219);
if (lean_is_scalar(x_226)) {
 x_231 = lean_alloc_ctor(0, 3, 0);
} else {
 x_231 = x_226;
}
lean_ctor_set(x_231, 0, x_219);
lean_ctor_set(x_231, 1, x_230);
lean_ctor_set(x_231, 2, x_221);
x_232 = lean_nat_dec_lt(x_228, x_229);
if (x_232 == 0)
{
lean_object* x_233; 
lean_dec(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_212);
lean_dec_ref(x_211);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_17, 0, x_215);
lean_ctor_set(x_16, 0, x_223);
lean_ctor_set(x_15, 0, x_231);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_8);
lean_ctor_set(x_233, 1, x_14);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_234 = x_21;
} else {
 lean_dec_ref(x_21);
 x_234 = lean_box(0);
}
x_235 = lean_array_fget(x_35, x_36);
lean_dec(x_36);
lean_dec_ref(x_35);
x_236 = lean_array_fget(x_44, x_45);
lean_dec(x_45);
lean_dec_ref(x_44);
x_237 = lean_array_fget(x_211, x_212);
lean_dec(x_212);
lean_dec_ref(x_211);
x_238 = lean_array_fget(x_219, x_220);
lean_dec(x_220);
lean_dec_ref(x_219);
x_239 = lean_array_fget(x_227, x_228);
x_240 = lean_box(x_2);
x_241 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_242 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_242, 0, x_235);
lean_closure_set(x_242, 1, x_1);
lean_closure_set(x_242, 2, x_9);
lean_closure_set(x_242, 3, x_240);
lean_closure_set(x_242, 4, x_241);
lean_closure_set(x_242, 5, x_239);
lean_closure_set(x_242, 6, x_4);
lean_closure_set(x_242, 7, x_5);
lean_closure_set(x_242, 8, x_237);
x_243 = lean_nat_sub(x_238, x_5);
lean_dec(x_238);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_6);
x_244 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg(x_236, x_243, x_6, x_242, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
x_248 = lean_nat_add(x_228, x_47);
lean_dec(x_228);
if (lean_is_scalar(x_234)) {
 x_249 = lean_alloc_ctor(0, 3, 0);
} else {
 x_249 = x_234;
}
lean_ctor_set(x_249, 0, x_227);
lean_ctor_set(x_249, 1, x_248);
lean_ctor_set(x_249, 2, x_229);
x_250 = lean_array_push(x_33, x_245);
lean_ctor_set(x_18, 1, x_250);
lean_ctor_set(x_17, 0, x_215);
lean_ctor_set(x_16, 0, x_223);
lean_ctor_set(x_15, 0, x_231);
lean_ctor_set(x_8, 0, x_249);
x_251 = lean_nat_add(x_9, x_47);
lean_dec(x_9);
x_252 = lean_nat_dec_lt(x_251, x_7);
if (x_252 == 0)
{
lean_object* x_253; 
lean_dec(x_251);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_247)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_247;
}
lean_ctor_set(x_253, 0, x_8);
lean_ctor_set(x_253, 1, x_246);
return x_253;
}
else
{
lean_dec(x_247);
x_9 = x_251;
x_14 = x_246;
goto _start;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_234);
lean_dec_ref(x_231);
lean_dec(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_223);
lean_dec_ref(x_215);
lean_dec_ref(x_19);
lean_free_object(x_18);
lean_dec(x_33);
lean_free_object(x_17);
lean_free_object(x_16);
lean_free_object(x_15);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_255 = lean_ctor_get(x_244, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_244, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_257 = x_244;
} else {
 lean_dec_ref(x_244);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
}
}
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
lean_dec(x_19);
x_259 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_259);
x_260 = lean_ctor_get(x_30, 1);
lean_inc(x_260);
x_261 = lean_ctor_get(x_30, 2);
lean_inc(x_261);
x_262 = lean_unsigned_to_nat(1u);
x_263 = lean_nat_add(x_36, x_262);
lean_inc_ref(x_35);
x_264 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_264, 0, x_35);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set(x_264, 2, x_37);
x_265 = lean_nat_dec_lt(x_260, x_261);
if (x_265 == 0)
{
lean_object* x_266; 
lean_dec(x_261);
lean_dec(x_260);
lean_dec_ref(x_259);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_18, 0, x_264);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_8);
lean_ctor_set(x_266, 1, x_14);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; 
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 x_267 = x_30;
} else {
 lean_dec_ref(x_30);
 x_267 = lean_box(0);
}
x_268 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_268);
x_269 = lean_ctor_get(x_27, 1);
lean_inc(x_269);
x_270 = lean_ctor_get(x_27, 2);
lean_inc(x_270);
x_271 = lean_nat_add(x_260, x_262);
lean_inc_ref(x_259);
if (lean_is_scalar(x_267)) {
 x_272 = lean_alloc_ctor(0, 3, 0);
} else {
 x_272 = x_267;
}
lean_ctor_set(x_272, 0, x_259);
lean_ctor_set(x_272, 1, x_271);
lean_ctor_set(x_272, 2, x_261);
x_273 = lean_nat_dec_lt(x_269, x_270);
if (x_273 == 0)
{
lean_object* x_274; 
lean_dec(x_270);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_260);
lean_dec_ref(x_259);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_18, 0, x_264);
lean_ctor_set(x_17, 0, x_272);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_8);
lean_ctor_set(x_274, 1, x_14);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 x_275 = x_27;
} else {
 lean_dec_ref(x_27);
 x_275 = lean_box(0);
}
x_276 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_276);
x_277 = lean_ctor_get(x_24, 1);
lean_inc(x_277);
x_278 = lean_ctor_get(x_24, 2);
lean_inc(x_278);
x_279 = lean_nat_add(x_269, x_262);
lean_inc_ref(x_268);
if (lean_is_scalar(x_275)) {
 x_280 = lean_alloc_ctor(0, 3, 0);
} else {
 x_280 = x_275;
}
lean_ctor_set(x_280, 0, x_268);
lean_ctor_set(x_280, 1, x_279);
lean_ctor_set(x_280, 2, x_270);
x_281 = lean_nat_dec_lt(x_277, x_278);
if (x_281 == 0)
{
lean_object* x_282; 
lean_dec(x_278);
lean_dec(x_277);
lean_dec_ref(x_276);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_260);
lean_dec_ref(x_259);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_18, 0, x_264);
lean_ctor_set(x_17, 0, x_272);
lean_ctor_set(x_16, 0, x_280);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_8);
lean_ctor_set(x_282, 1, x_14);
return x_282;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 x_283 = x_24;
} else {
 lean_dec_ref(x_24);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_284);
x_285 = lean_ctor_get(x_21, 1);
lean_inc(x_285);
x_286 = lean_ctor_get(x_21, 2);
lean_inc(x_286);
x_287 = lean_nat_add(x_277, x_262);
lean_inc_ref(x_276);
if (lean_is_scalar(x_283)) {
 x_288 = lean_alloc_ctor(0, 3, 0);
} else {
 x_288 = x_283;
}
lean_ctor_set(x_288, 0, x_276);
lean_ctor_set(x_288, 1, x_287);
lean_ctor_set(x_288, 2, x_278);
x_289 = lean_nat_dec_lt(x_285, x_286);
if (x_289 == 0)
{
lean_object* x_290; 
lean_dec(x_286);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec(x_277);
lean_dec_ref(x_276);
lean_dec(x_269);
lean_dec_ref(x_268);
lean_dec(x_260);
lean_dec_ref(x_259);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_18, 0, x_264);
lean_ctor_set(x_17, 0, x_272);
lean_ctor_set(x_16, 0, x_280);
lean_ctor_set(x_15, 0, x_288);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_8);
lean_ctor_set(x_290, 1, x_14);
return x_290;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_291 = x_21;
} else {
 lean_dec_ref(x_21);
 x_291 = lean_box(0);
}
x_292 = lean_array_fget(x_35, x_36);
lean_dec(x_36);
lean_dec_ref(x_35);
x_293 = lean_array_fget(x_259, x_260);
lean_dec(x_260);
lean_dec_ref(x_259);
x_294 = lean_array_fget(x_268, x_269);
lean_dec(x_269);
lean_dec_ref(x_268);
x_295 = lean_array_fget(x_276, x_277);
lean_dec(x_277);
lean_dec_ref(x_276);
x_296 = lean_array_fget(x_284, x_285);
x_297 = lean_box(x_2);
x_298 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_299 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_299, 0, x_292);
lean_closure_set(x_299, 1, x_1);
lean_closure_set(x_299, 2, x_9);
lean_closure_set(x_299, 3, x_297);
lean_closure_set(x_299, 4, x_298);
lean_closure_set(x_299, 5, x_296);
lean_closure_set(x_299, 6, x_4);
lean_closure_set(x_299, 7, x_5);
lean_closure_set(x_299, 8, x_294);
x_300 = lean_nat_sub(x_295, x_5);
lean_dec(x_295);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_6);
x_301 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg(x_293, x_300, x_6, x_299, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_304 = x_301;
} else {
 lean_dec_ref(x_301);
 x_304 = lean_box(0);
}
x_305 = lean_nat_add(x_285, x_262);
lean_dec(x_285);
if (lean_is_scalar(x_291)) {
 x_306 = lean_alloc_ctor(0, 3, 0);
} else {
 x_306 = x_291;
}
lean_ctor_set(x_306, 0, x_284);
lean_ctor_set(x_306, 1, x_305);
lean_ctor_set(x_306, 2, x_286);
x_307 = lean_array_push(x_33, x_302);
lean_ctor_set(x_18, 1, x_307);
lean_ctor_set(x_18, 0, x_264);
lean_ctor_set(x_17, 0, x_272);
lean_ctor_set(x_16, 0, x_280);
lean_ctor_set(x_15, 0, x_288);
lean_ctor_set(x_8, 0, x_306);
x_308 = lean_nat_add(x_9, x_262);
lean_dec(x_9);
x_309 = lean_nat_dec_lt(x_308, x_7);
if (x_309 == 0)
{
lean_object* x_310; 
lean_dec(x_308);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_304)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_304;
}
lean_ctor_set(x_310, 0, x_8);
lean_ctor_set(x_310, 1, x_303);
return x_310;
}
else
{
lean_dec(x_304);
x_9 = x_308;
x_14 = x_303;
goto _start;
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_291);
lean_dec_ref(x_288);
lean_dec(x_286);
lean_dec(x_285);
lean_dec_ref(x_284);
lean_dec_ref(x_280);
lean_dec_ref(x_272);
lean_dec_ref(x_264);
lean_free_object(x_18);
lean_dec(x_33);
lean_free_object(x_17);
lean_free_object(x_16);
lean_free_object(x_15);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_312 = lean_ctor_get(x_301, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_301, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_314 = x_301;
} else {
 lean_dec_ref(x_301);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(1, 2, 0);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_312);
lean_ctor_set(x_315, 1, x_313);
return x_315;
}
}
}
}
}
}
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; 
x_316 = lean_ctor_get(x_18, 1);
lean_inc(x_316);
lean_dec(x_18);
x_317 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_317);
x_318 = lean_ctor_get(x_19, 1);
lean_inc(x_318);
x_319 = lean_ctor_get(x_19, 2);
lean_inc(x_319);
x_320 = lean_nat_dec_lt(x_318, x_319);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; 
lean_dec(x_319);
lean_dec(x_318);
lean_dec_ref(x_317);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_19);
lean_ctor_set(x_321, 1, x_316);
lean_ctor_set(x_17, 1, x_321);
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_8);
lean_ctor_set(x_322, 1, x_14);
return x_322;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_323 = x_19;
} else {
 lean_dec_ref(x_19);
 x_323 = lean_box(0);
}
x_324 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_324);
x_325 = lean_ctor_get(x_30, 1);
lean_inc(x_325);
x_326 = lean_ctor_get(x_30, 2);
lean_inc(x_326);
x_327 = lean_unsigned_to_nat(1u);
x_328 = lean_nat_add(x_318, x_327);
lean_inc_ref(x_317);
if (lean_is_scalar(x_323)) {
 x_329 = lean_alloc_ctor(0, 3, 0);
} else {
 x_329 = x_323;
}
lean_ctor_set(x_329, 0, x_317);
lean_ctor_set(x_329, 1, x_328);
lean_ctor_set(x_329, 2, x_319);
x_330 = lean_nat_dec_lt(x_325, x_326);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; 
lean_dec(x_326);
lean_dec(x_325);
lean_dec_ref(x_324);
lean_dec(x_318);
lean_dec_ref(x_317);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_316);
lean_ctor_set(x_17, 1, x_331);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_8);
lean_ctor_set(x_332, 1, x_14);
return x_332;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 x_333 = x_30;
} else {
 lean_dec_ref(x_30);
 x_333 = lean_box(0);
}
x_334 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_334);
x_335 = lean_ctor_get(x_27, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_27, 2);
lean_inc(x_336);
x_337 = lean_nat_add(x_325, x_327);
lean_inc_ref(x_324);
if (lean_is_scalar(x_333)) {
 x_338 = lean_alloc_ctor(0, 3, 0);
} else {
 x_338 = x_333;
}
lean_ctor_set(x_338, 0, x_324);
lean_ctor_set(x_338, 1, x_337);
lean_ctor_set(x_338, 2, x_326);
x_339 = lean_nat_dec_lt(x_335, x_336);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; 
lean_dec(x_336);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec(x_325);
lean_dec_ref(x_324);
lean_dec(x_318);
lean_dec_ref(x_317);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_329);
lean_ctor_set(x_340, 1, x_316);
lean_ctor_set(x_17, 1, x_340);
lean_ctor_set(x_17, 0, x_338);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_8);
lean_ctor_set(x_341, 1, x_14);
return x_341;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 x_342 = x_27;
} else {
 lean_dec_ref(x_27);
 x_342 = lean_box(0);
}
x_343 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_343);
x_344 = lean_ctor_get(x_24, 1);
lean_inc(x_344);
x_345 = lean_ctor_get(x_24, 2);
lean_inc(x_345);
x_346 = lean_nat_add(x_335, x_327);
lean_inc_ref(x_334);
if (lean_is_scalar(x_342)) {
 x_347 = lean_alloc_ctor(0, 3, 0);
} else {
 x_347 = x_342;
}
lean_ctor_set(x_347, 0, x_334);
lean_ctor_set(x_347, 1, x_346);
lean_ctor_set(x_347, 2, x_336);
x_348 = lean_nat_dec_lt(x_344, x_345);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; 
lean_dec(x_345);
lean_dec(x_344);
lean_dec_ref(x_343);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec(x_325);
lean_dec_ref(x_324);
lean_dec(x_318);
lean_dec_ref(x_317);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_329);
lean_ctor_set(x_349, 1, x_316);
lean_ctor_set(x_17, 1, x_349);
lean_ctor_set(x_17, 0, x_338);
lean_ctor_set(x_16, 0, x_347);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_8);
lean_ctor_set(x_350, 1, x_14);
return x_350;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 x_351 = x_24;
} else {
 lean_dec_ref(x_24);
 x_351 = lean_box(0);
}
x_352 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_352);
x_353 = lean_ctor_get(x_21, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_21, 2);
lean_inc(x_354);
x_355 = lean_nat_add(x_344, x_327);
lean_inc_ref(x_343);
if (lean_is_scalar(x_351)) {
 x_356 = lean_alloc_ctor(0, 3, 0);
} else {
 x_356 = x_351;
}
lean_ctor_set(x_356, 0, x_343);
lean_ctor_set(x_356, 1, x_355);
lean_ctor_set(x_356, 2, x_345);
x_357 = lean_nat_dec_lt(x_353, x_354);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; 
lean_dec(x_354);
lean_dec(x_353);
lean_dec_ref(x_352);
lean_dec(x_344);
lean_dec_ref(x_343);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec(x_325);
lean_dec_ref(x_324);
lean_dec(x_318);
lean_dec_ref(x_317);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_329);
lean_ctor_set(x_358, 1, x_316);
lean_ctor_set(x_17, 1, x_358);
lean_ctor_set(x_17, 0, x_338);
lean_ctor_set(x_16, 0, x_347);
lean_ctor_set(x_15, 0, x_356);
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_8);
lean_ctor_set(x_359, 1, x_14);
return x_359;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_360 = x_21;
} else {
 lean_dec_ref(x_21);
 x_360 = lean_box(0);
}
x_361 = lean_array_fget(x_317, x_318);
lean_dec(x_318);
lean_dec_ref(x_317);
x_362 = lean_array_fget(x_324, x_325);
lean_dec(x_325);
lean_dec_ref(x_324);
x_363 = lean_array_fget(x_334, x_335);
lean_dec(x_335);
lean_dec_ref(x_334);
x_364 = lean_array_fget(x_343, x_344);
lean_dec(x_344);
lean_dec_ref(x_343);
x_365 = lean_array_fget(x_352, x_353);
x_366 = lean_box(x_2);
x_367 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_368 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_368, 0, x_361);
lean_closure_set(x_368, 1, x_1);
lean_closure_set(x_368, 2, x_9);
lean_closure_set(x_368, 3, x_366);
lean_closure_set(x_368, 4, x_367);
lean_closure_set(x_368, 5, x_365);
lean_closure_set(x_368, 6, x_4);
lean_closure_set(x_368, 7, x_5);
lean_closure_set(x_368, 8, x_363);
x_369 = lean_nat_sub(x_364, x_5);
lean_dec(x_364);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_6);
x_370 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg(x_362, x_369, x_6, x_368, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_373 = x_370;
} else {
 lean_dec_ref(x_370);
 x_373 = lean_box(0);
}
x_374 = lean_nat_add(x_353, x_327);
lean_dec(x_353);
if (lean_is_scalar(x_360)) {
 x_375 = lean_alloc_ctor(0, 3, 0);
} else {
 x_375 = x_360;
}
lean_ctor_set(x_375, 0, x_352);
lean_ctor_set(x_375, 1, x_374);
lean_ctor_set(x_375, 2, x_354);
x_376 = lean_array_push(x_316, x_371);
x_377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_377, 0, x_329);
lean_ctor_set(x_377, 1, x_376);
lean_ctor_set(x_17, 1, x_377);
lean_ctor_set(x_17, 0, x_338);
lean_ctor_set(x_16, 0, x_347);
lean_ctor_set(x_15, 0, x_356);
lean_ctor_set(x_8, 0, x_375);
x_378 = lean_nat_add(x_9, x_327);
lean_dec(x_9);
x_379 = lean_nat_dec_lt(x_378, x_7);
if (x_379 == 0)
{
lean_object* x_380; 
lean_dec(x_378);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_373)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_373;
}
lean_ctor_set(x_380, 0, x_8);
lean_ctor_set(x_380, 1, x_372);
return x_380;
}
else
{
lean_dec(x_373);
x_9 = x_378;
x_14 = x_372;
goto _start;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_360);
lean_dec_ref(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec_ref(x_352);
lean_dec_ref(x_347);
lean_dec_ref(x_338);
lean_dec_ref(x_329);
lean_dec(x_316);
lean_free_object(x_17);
lean_free_object(x_16);
lean_free_object(x_15);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_382 = lean_ctor_get(x_370, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_370, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_384 = x_370;
} else {
 lean_dec_ref(x_370);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(1, 2, 0);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_382);
lean_ctor_set(x_385, 1, x_383);
return x_385;
}
}
}
}
}
}
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; 
x_386 = lean_ctor_get(x_17, 0);
lean_inc(x_386);
lean_dec(x_17);
x_387 = lean_ctor_get(x_18, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_388 = x_18;
} else {
 lean_dec_ref(x_18);
 x_388 = lean_box(0);
}
x_389 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_389);
x_390 = lean_ctor_get(x_19, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_19, 2);
lean_inc(x_391);
x_392 = lean_nat_dec_lt(x_390, x_391);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_391);
lean_dec(x_390);
lean_dec_ref(x_389);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_388)) {
 x_393 = lean_alloc_ctor(0, 2, 0);
} else {
 x_393 = x_388;
}
lean_ctor_set(x_393, 0, x_19);
lean_ctor_set(x_393, 1, x_387);
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_386);
lean_ctor_set(x_394, 1, x_393);
lean_ctor_set(x_16, 1, x_394);
x_395 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_395, 0, x_8);
lean_ctor_set(x_395, 1, x_14);
return x_395;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; 
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_396 = x_19;
} else {
 lean_dec_ref(x_19);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_386, 0);
lean_inc_ref(x_397);
x_398 = lean_ctor_get(x_386, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_386, 2);
lean_inc(x_399);
x_400 = lean_unsigned_to_nat(1u);
x_401 = lean_nat_add(x_390, x_400);
lean_inc_ref(x_389);
if (lean_is_scalar(x_396)) {
 x_402 = lean_alloc_ctor(0, 3, 0);
} else {
 x_402 = x_396;
}
lean_ctor_set(x_402, 0, x_389);
lean_ctor_set(x_402, 1, x_401);
lean_ctor_set(x_402, 2, x_391);
x_403 = lean_nat_dec_lt(x_398, x_399);
if (x_403 == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_399);
lean_dec(x_398);
lean_dec_ref(x_397);
lean_dec(x_390);
lean_dec_ref(x_389);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_388)) {
 x_404 = lean_alloc_ctor(0, 2, 0);
} else {
 x_404 = x_388;
}
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_387);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_386);
lean_ctor_set(x_405, 1, x_404);
lean_ctor_set(x_16, 1, x_405);
x_406 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_406, 0, x_8);
lean_ctor_set(x_406, 1, x_14);
return x_406;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 lean_ctor_release(x_386, 2);
 x_407 = x_386;
} else {
 lean_dec_ref(x_386);
 x_407 = lean_box(0);
}
x_408 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_408);
x_409 = lean_ctor_get(x_27, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_27, 2);
lean_inc(x_410);
x_411 = lean_nat_add(x_398, x_400);
lean_inc_ref(x_397);
if (lean_is_scalar(x_407)) {
 x_412 = lean_alloc_ctor(0, 3, 0);
} else {
 x_412 = x_407;
}
lean_ctor_set(x_412, 0, x_397);
lean_ctor_set(x_412, 1, x_411);
lean_ctor_set(x_412, 2, x_399);
x_413 = lean_nat_dec_lt(x_409, x_410);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
lean_dec(x_410);
lean_dec(x_409);
lean_dec_ref(x_408);
lean_dec(x_398);
lean_dec_ref(x_397);
lean_dec(x_390);
lean_dec_ref(x_389);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_388)) {
 x_414 = lean_alloc_ctor(0, 2, 0);
} else {
 x_414 = x_388;
}
lean_ctor_set(x_414, 0, x_402);
lean_ctor_set(x_414, 1, x_387);
x_415 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_415, 0, x_412);
lean_ctor_set(x_415, 1, x_414);
lean_ctor_set(x_16, 1, x_415);
x_416 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_416, 0, x_8);
lean_ctor_set(x_416, 1, x_14);
return x_416;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; 
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 x_417 = x_27;
} else {
 lean_dec_ref(x_27);
 x_417 = lean_box(0);
}
x_418 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_418);
x_419 = lean_ctor_get(x_24, 1);
lean_inc(x_419);
x_420 = lean_ctor_get(x_24, 2);
lean_inc(x_420);
x_421 = lean_nat_add(x_409, x_400);
lean_inc_ref(x_408);
if (lean_is_scalar(x_417)) {
 x_422 = lean_alloc_ctor(0, 3, 0);
} else {
 x_422 = x_417;
}
lean_ctor_set(x_422, 0, x_408);
lean_ctor_set(x_422, 1, x_421);
lean_ctor_set(x_422, 2, x_410);
x_423 = lean_nat_dec_lt(x_419, x_420);
if (x_423 == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_420);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_409);
lean_dec_ref(x_408);
lean_dec(x_398);
lean_dec_ref(x_397);
lean_dec(x_390);
lean_dec_ref(x_389);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_388)) {
 x_424 = lean_alloc_ctor(0, 2, 0);
} else {
 x_424 = x_388;
}
lean_ctor_set(x_424, 0, x_402);
lean_ctor_set(x_424, 1, x_387);
x_425 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_425, 0, x_412);
lean_ctor_set(x_425, 1, x_424);
lean_ctor_set(x_16, 1, x_425);
lean_ctor_set(x_16, 0, x_422);
x_426 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_426, 0, x_8);
lean_ctor_set(x_426, 1, x_14);
return x_426;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; 
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 x_427 = x_24;
} else {
 lean_dec_ref(x_24);
 x_427 = lean_box(0);
}
x_428 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_428);
x_429 = lean_ctor_get(x_21, 1);
lean_inc(x_429);
x_430 = lean_ctor_get(x_21, 2);
lean_inc(x_430);
x_431 = lean_nat_add(x_419, x_400);
lean_inc_ref(x_418);
if (lean_is_scalar(x_427)) {
 x_432 = lean_alloc_ctor(0, 3, 0);
} else {
 x_432 = x_427;
}
lean_ctor_set(x_432, 0, x_418);
lean_ctor_set(x_432, 1, x_431);
lean_ctor_set(x_432, 2, x_420);
x_433 = lean_nat_dec_lt(x_429, x_430);
if (x_433 == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_430);
lean_dec(x_429);
lean_dec_ref(x_428);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_409);
lean_dec_ref(x_408);
lean_dec(x_398);
lean_dec_ref(x_397);
lean_dec(x_390);
lean_dec_ref(x_389);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_388)) {
 x_434 = lean_alloc_ctor(0, 2, 0);
} else {
 x_434 = x_388;
}
lean_ctor_set(x_434, 0, x_402);
lean_ctor_set(x_434, 1, x_387);
x_435 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_435, 0, x_412);
lean_ctor_set(x_435, 1, x_434);
lean_ctor_set(x_16, 1, x_435);
lean_ctor_set(x_16, 0, x_422);
lean_ctor_set(x_15, 0, x_432);
x_436 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_436, 0, x_8);
lean_ctor_set(x_436, 1, x_14);
return x_436;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_437 = x_21;
} else {
 lean_dec_ref(x_21);
 x_437 = lean_box(0);
}
x_438 = lean_array_fget(x_389, x_390);
lean_dec(x_390);
lean_dec_ref(x_389);
x_439 = lean_array_fget(x_397, x_398);
lean_dec(x_398);
lean_dec_ref(x_397);
x_440 = lean_array_fget(x_408, x_409);
lean_dec(x_409);
lean_dec_ref(x_408);
x_441 = lean_array_fget(x_418, x_419);
lean_dec(x_419);
lean_dec_ref(x_418);
x_442 = lean_array_fget(x_428, x_429);
x_443 = lean_box(x_2);
x_444 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_445 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_445, 0, x_438);
lean_closure_set(x_445, 1, x_1);
lean_closure_set(x_445, 2, x_9);
lean_closure_set(x_445, 3, x_443);
lean_closure_set(x_445, 4, x_444);
lean_closure_set(x_445, 5, x_442);
lean_closure_set(x_445, 6, x_4);
lean_closure_set(x_445, 7, x_5);
lean_closure_set(x_445, 8, x_440);
x_446 = lean_nat_sub(x_441, x_5);
lean_dec(x_441);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_6);
x_447 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg(x_439, x_446, x_6, x_445, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; 
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_450 = x_447;
} else {
 lean_dec_ref(x_447);
 x_450 = lean_box(0);
}
x_451 = lean_nat_add(x_429, x_400);
lean_dec(x_429);
if (lean_is_scalar(x_437)) {
 x_452 = lean_alloc_ctor(0, 3, 0);
} else {
 x_452 = x_437;
}
lean_ctor_set(x_452, 0, x_428);
lean_ctor_set(x_452, 1, x_451);
lean_ctor_set(x_452, 2, x_430);
x_453 = lean_array_push(x_387, x_448);
if (lean_is_scalar(x_388)) {
 x_454 = lean_alloc_ctor(0, 2, 0);
} else {
 x_454 = x_388;
}
lean_ctor_set(x_454, 0, x_402);
lean_ctor_set(x_454, 1, x_453);
x_455 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_455, 0, x_412);
lean_ctor_set(x_455, 1, x_454);
lean_ctor_set(x_16, 1, x_455);
lean_ctor_set(x_16, 0, x_422);
lean_ctor_set(x_15, 0, x_432);
lean_ctor_set(x_8, 0, x_452);
x_456 = lean_nat_add(x_9, x_400);
lean_dec(x_9);
x_457 = lean_nat_dec_lt(x_456, x_7);
if (x_457 == 0)
{
lean_object* x_458; 
lean_dec(x_456);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_450)) {
 x_458 = lean_alloc_ctor(0, 2, 0);
} else {
 x_458 = x_450;
}
lean_ctor_set(x_458, 0, x_8);
lean_ctor_set(x_458, 1, x_449);
return x_458;
}
else
{
lean_dec(x_450);
x_9 = x_456;
x_14 = x_449;
goto _start;
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_437);
lean_dec_ref(x_432);
lean_dec(x_430);
lean_dec(x_429);
lean_dec_ref(x_428);
lean_dec_ref(x_422);
lean_dec_ref(x_412);
lean_dec_ref(x_402);
lean_dec(x_388);
lean_dec(x_387);
lean_free_object(x_16);
lean_free_object(x_15);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_460 = lean_ctor_get(x_447, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_447, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_462 = x_447;
} else {
 lean_dec_ref(x_447);
 x_462 = lean_box(0);
}
if (lean_is_scalar(x_462)) {
 x_463 = lean_alloc_ctor(1, 2, 0);
} else {
 x_463 = x_462;
}
lean_ctor_set(x_463, 0, x_460);
lean_ctor_set(x_463, 1, x_461);
return x_463;
}
}
}
}
}
}
}
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; 
x_464 = lean_ctor_get(x_16, 0);
lean_inc(x_464);
lean_dec(x_16);
x_465 = lean_ctor_get(x_17, 0);
lean_inc(x_465);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_466 = x_17;
} else {
 lean_dec_ref(x_17);
 x_466 = lean_box(0);
}
x_467 = lean_ctor_get(x_18, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_468 = x_18;
} else {
 lean_dec_ref(x_18);
 x_468 = lean_box(0);
}
x_469 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_469);
x_470 = lean_ctor_get(x_19, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_19, 2);
lean_inc(x_471);
x_472 = lean_nat_dec_lt(x_470, x_471);
if (x_472 == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_dec(x_471);
lean_dec(x_470);
lean_dec_ref(x_469);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_468)) {
 x_473 = lean_alloc_ctor(0, 2, 0);
} else {
 x_473 = x_468;
}
lean_ctor_set(x_473, 0, x_19);
lean_ctor_set(x_473, 1, x_467);
if (lean_is_scalar(x_466)) {
 x_474 = lean_alloc_ctor(0, 2, 0);
} else {
 x_474 = x_466;
}
lean_ctor_set(x_474, 0, x_465);
lean_ctor_set(x_474, 1, x_473);
x_475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_475, 0, x_464);
lean_ctor_set(x_475, 1, x_474);
lean_ctor_set(x_15, 1, x_475);
x_476 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_476, 0, x_8);
lean_ctor_set(x_476, 1, x_14);
return x_476;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; 
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_477 = x_19;
} else {
 lean_dec_ref(x_19);
 x_477 = lean_box(0);
}
x_478 = lean_ctor_get(x_465, 0);
lean_inc_ref(x_478);
x_479 = lean_ctor_get(x_465, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_465, 2);
lean_inc(x_480);
x_481 = lean_unsigned_to_nat(1u);
x_482 = lean_nat_add(x_470, x_481);
lean_inc_ref(x_469);
if (lean_is_scalar(x_477)) {
 x_483 = lean_alloc_ctor(0, 3, 0);
} else {
 x_483 = x_477;
}
lean_ctor_set(x_483, 0, x_469);
lean_ctor_set(x_483, 1, x_482);
lean_ctor_set(x_483, 2, x_471);
x_484 = lean_nat_dec_lt(x_479, x_480);
if (x_484 == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_480);
lean_dec(x_479);
lean_dec_ref(x_478);
lean_dec(x_470);
lean_dec_ref(x_469);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_468)) {
 x_485 = lean_alloc_ctor(0, 2, 0);
} else {
 x_485 = x_468;
}
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_467);
if (lean_is_scalar(x_466)) {
 x_486 = lean_alloc_ctor(0, 2, 0);
} else {
 x_486 = x_466;
}
lean_ctor_set(x_486, 0, x_465);
lean_ctor_set(x_486, 1, x_485);
x_487 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_487, 0, x_464);
lean_ctor_set(x_487, 1, x_486);
lean_ctor_set(x_15, 1, x_487);
x_488 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_488, 0, x_8);
lean_ctor_set(x_488, 1, x_14);
return x_488;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; 
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 lean_ctor_release(x_465, 2);
 x_489 = x_465;
} else {
 lean_dec_ref(x_465);
 x_489 = lean_box(0);
}
x_490 = lean_ctor_get(x_464, 0);
lean_inc_ref(x_490);
x_491 = lean_ctor_get(x_464, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_464, 2);
lean_inc(x_492);
x_493 = lean_nat_add(x_479, x_481);
lean_inc_ref(x_478);
if (lean_is_scalar(x_489)) {
 x_494 = lean_alloc_ctor(0, 3, 0);
} else {
 x_494 = x_489;
}
lean_ctor_set(x_494, 0, x_478);
lean_ctor_set(x_494, 1, x_493);
lean_ctor_set(x_494, 2, x_480);
x_495 = lean_nat_dec_lt(x_491, x_492);
if (x_495 == 0)
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
lean_dec(x_492);
lean_dec(x_491);
lean_dec_ref(x_490);
lean_dec(x_479);
lean_dec_ref(x_478);
lean_dec(x_470);
lean_dec_ref(x_469);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_468)) {
 x_496 = lean_alloc_ctor(0, 2, 0);
} else {
 x_496 = x_468;
}
lean_ctor_set(x_496, 0, x_483);
lean_ctor_set(x_496, 1, x_467);
if (lean_is_scalar(x_466)) {
 x_497 = lean_alloc_ctor(0, 2, 0);
} else {
 x_497 = x_466;
}
lean_ctor_set(x_497, 0, x_494);
lean_ctor_set(x_497, 1, x_496);
x_498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_498, 0, x_464);
lean_ctor_set(x_498, 1, x_497);
lean_ctor_set(x_15, 1, x_498);
x_499 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_499, 0, x_8);
lean_ctor_set(x_499, 1, x_14);
return x_499;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; 
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 x_500 = x_464;
} else {
 lean_dec_ref(x_464);
 x_500 = lean_box(0);
}
x_501 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_501);
x_502 = lean_ctor_get(x_24, 1);
lean_inc(x_502);
x_503 = lean_ctor_get(x_24, 2);
lean_inc(x_503);
x_504 = lean_nat_add(x_491, x_481);
lean_inc_ref(x_490);
if (lean_is_scalar(x_500)) {
 x_505 = lean_alloc_ctor(0, 3, 0);
} else {
 x_505 = x_500;
}
lean_ctor_set(x_505, 0, x_490);
lean_ctor_set(x_505, 1, x_504);
lean_ctor_set(x_505, 2, x_492);
x_506 = lean_nat_dec_lt(x_502, x_503);
if (x_506 == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec(x_503);
lean_dec(x_502);
lean_dec_ref(x_501);
lean_dec(x_491);
lean_dec_ref(x_490);
lean_dec(x_479);
lean_dec_ref(x_478);
lean_dec(x_470);
lean_dec_ref(x_469);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_468)) {
 x_507 = lean_alloc_ctor(0, 2, 0);
} else {
 x_507 = x_468;
}
lean_ctor_set(x_507, 0, x_483);
lean_ctor_set(x_507, 1, x_467);
if (lean_is_scalar(x_466)) {
 x_508 = lean_alloc_ctor(0, 2, 0);
} else {
 x_508 = x_466;
}
lean_ctor_set(x_508, 0, x_494);
lean_ctor_set(x_508, 1, x_507);
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_505);
lean_ctor_set(x_509, 1, x_508);
lean_ctor_set(x_15, 1, x_509);
x_510 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_510, 0, x_8);
lean_ctor_set(x_510, 1, x_14);
return x_510;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_517; 
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 x_511 = x_24;
} else {
 lean_dec_ref(x_24);
 x_511 = lean_box(0);
}
x_512 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_512);
x_513 = lean_ctor_get(x_21, 1);
lean_inc(x_513);
x_514 = lean_ctor_get(x_21, 2);
lean_inc(x_514);
x_515 = lean_nat_add(x_502, x_481);
lean_inc_ref(x_501);
if (lean_is_scalar(x_511)) {
 x_516 = lean_alloc_ctor(0, 3, 0);
} else {
 x_516 = x_511;
}
lean_ctor_set(x_516, 0, x_501);
lean_ctor_set(x_516, 1, x_515);
lean_ctor_set(x_516, 2, x_503);
x_517 = lean_nat_dec_lt(x_513, x_514);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_514);
lean_dec(x_513);
lean_dec_ref(x_512);
lean_dec(x_502);
lean_dec_ref(x_501);
lean_dec(x_491);
lean_dec_ref(x_490);
lean_dec(x_479);
lean_dec_ref(x_478);
lean_dec(x_470);
lean_dec_ref(x_469);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_468)) {
 x_518 = lean_alloc_ctor(0, 2, 0);
} else {
 x_518 = x_468;
}
lean_ctor_set(x_518, 0, x_483);
lean_ctor_set(x_518, 1, x_467);
if (lean_is_scalar(x_466)) {
 x_519 = lean_alloc_ctor(0, 2, 0);
} else {
 x_519 = x_466;
}
lean_ctor_set(x_519, 0, x_494);
lean_ctor_set(x_519, 1, x_518);
x_520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_520, 0, x_505);
lean_ctor_set(x_520, 1, x_519);
lean_ctor_set(x_15, 1, x_520);
lean_ctor_set(x_15, 0, x_516);
x_521 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_521, 0, x_8);
lean_ctor_set(x_521, 1, x_14);
return x_521;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_522 = x_21;
} else {
 lean_dec_ref(x_21);
 x_522 = lean_box(0);
}
x_523 = lean_array_fget(x_469, x_470);
lean_dec(x_470);
lean_dec_ref(x_469);
x_524 = lean_array_fget(x_478, x_479);
lean_dec(x_479);
lean_dec_ref(x_478);
x_525 = lean_array_fget(x_490, x_491);
lean_dec(x_491);
lean_dec_ref(x_490);
x_526 = lean_array_fget(x_501, x_502);
lean_dec(x_502);
lean_dec_ref(x_501);
x_527 = lean_array_fget(x_512, x_513);
x_528 = lean_box(x_2);
x_529 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_530 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_530, 0, x_523);
lean_closure_set(x_530, 1, x_1);
lean_closure_set(x_530, 2, x_9);
lean_closure_set(x_530, 3, x_528);
lean_closure_set(x_530, 4, x_529);
lean_closure_set(x_530, 5, x_527);
lean_closure_set(x_530, 6, x_4);
lean_closure_set(x_530, 7, x_5);
lean_closure_set(x_530, 8, x_525);
x_531 = lean_nat_sub(x_526, x_5);
lean_dec(x_526);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_6);
x_532 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg(x_524, x_531, x_6, x_530, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; uint8_t x_543; 
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_532, 1);
lean_inc(x_534);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_535 = x_532;
} else {
 lean_dec_ref(x_532);
 x_535 = lean_box(0);
}
x_536 = lean_nat_add(x_513, x_481);
lean_dec(x_513);
if (lean_is_scalar(x_522)) {
 x_537 = lean_alloc_ctor(0, 3, 0);
} else {
 x_537 = x_522;
}
lean_ctor_set(x_537, 0, x_512);
lean_ctor_set(x_537, 1, x_536);
lean_ctor_set(x_537, 2, x_514);
x_538 = lean_array_push(x_467, x_533);
if (lean_is_scalar(x_468)) {
 x_539 = lean_alloc_ctor(0, 2, 0);
} else {
 x_539 = x_468;
}
lean_ctor_set(x_539, 0, x_483);
lean_ctor_set(x_539, 1, x_538);
if (lean_is_scalar(x_466)) {
 x_540 = lean_alloc_ctor(0, 2, 0);
} else {
 x_540 = x_466;
}
lean_ctor_set(x_540, 0, x_494);
lean_ctor_set(x_540, 1, x_539);
x_541 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_541, 0, x_505);
lean_ctor_set(x_541, 1, x_540);
lean_ctor_set(x_15, 1, x_541);
lean_ctor_set(x_15, 0, x_516);
lean_ctor_set(x_8, 0, x_537);
x_542 = lean_nat_add(x_9, x_481);
lean_dec(x_9);
x_543 = lean_nat_dec_lt(x_542, x_7);
if (x_543 == 0)
{
lean_object* x_544; 
lean_dec(x_542);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_535)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_535;
}
lean_ctor_set(x_544, 0, x_8);
lean_ctor_set(x_544, 1, x_534);
return x_544;
}
else
{
lean_dec(x_535);
x_9 = x_542;
x_14 = x_534;
goto _start;
}
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec(x_522);
lean_dec_ref(x_516);
lean_dec(x_514);
lean_dec(x_513);
lean_dec_ref(x_512);
lean_dec_ref(x_505);
lean_dec_ref(x_494);
lean_dec_ref(x_483);
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_466);
lean_free_object(x_15);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_546 = lean_ctor_get(x_532, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_532, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_548 = x_532;
} else {
 lean_dec_ref(x_532);
 x_548 = lean_box(0);
}
if (lean_is_scalar(x_548)) {
 x_549 = lean_alloc_ctor(1, 2, 0);
} else {
 x_549 = x_548;
}
lean_ctor_set(x_549, 0, x_546);
lean_ctor_set(x_549, 1, x_547);
return x_549;
}
}
}
}
}
}
}
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; uint8_t x_560; 
x_550 = lean_ctor_get(x_15, 0);
lean_inc(x_550);
lean_dec(x_15);
x_551 = lean_ctor_get(x_16, 0);
lean_inc(x_551);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_552 = x_16;
} else {
 lean_dec_ref(x_16);
 x_552 = lean_box(0);
}
x_553 = lean_ctor_get(x_17, 0);
lean_inc(x_553);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_554 = x_17;
} else {
 lean_dec_ref(x_17);
 x_554 = lean_box(0);
}
x_555 = lean_ctor_get(x_18, 1);
lean_inc(x_555);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_556 = x_18;
} else {
 lean_dec_ref(x_18);
 x_556 = lean_box(0);
}
x_557 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_557);
x_558 = lean_ctor_get(x_19, 1);
lean_inc(x_558);
x_559 = lean_ctor_get(x_19, 2);
lean_inc(x_559);
x_560 = lean_nat_dec_lt(x_558, x_559);
if (x_560 == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_dec(x_559);
lean_dec(x_558);
lean_dec_ref(x_557);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_556)) {
 x_561 = lean_alloc_ctor(0, 2, 0);
} else {
 x_561 = x_556;
}
lean_ctor_set(x_561, 0, x_19);
lean_ctor_set(x_561, 1, x_555);
if (lean_is_scalar(x_554)) {
 x_562 = lean_alloc_ctor(0, 2, 0);
} else {
 x_562 = x_554;
}
lean_ctor_set(x_562, 0, x_553);
lean_ctor_set(x_562, 1, x_561);
if (lean_is_scalar(x_552)) {
 x_563 = lean_alloc_ctor(0, 2, 0);
} else {
 x_563 = x_552;
}
lean_ctor_set(x_563, 0, x_551);
lean_ctor_set(x_563, 1, x_562);
x_564 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_564, 0, x_550);
lean_ctor_set(x_564, 1, x_563);
lean_ctor_set(x_8, 1, x_564);
x_565 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_565, 0, x_8);
lean_ctor_set(x_565, 1, x_14);
return x_565;
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; uint8_t x_573; 
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_566 = x_19;
} else {
 lean_dec_ref(x_19);
 x_566 = lean_box(0);
}
x_567 = lean_ctor_get(x_553, 0);
lean_inc_ref(x_567);
x_568 = lean_ctor_get(x_553, 1);
lean_inc(x_568);
x_569 = lean_ctor_get(x_553, 2);
lean_inc(x_569);
x_570 = lean_unsigned_to_nat(1u);
x_571 = lean_nat_add(x_558, x_570);
lean_inc_ref(x_557);
if (lean_is_scalar(x_566)) {
 x_572 = lean_alloc_ctor(0, 3, 0);
} else {
 x_572 = x_566;
}
lean_ctor_set(x_572, 0, x_557);
lean_ctor_set(x_572, 1, x_571);
lean_ctor_set(x_572, 2, x_559);
x_573 = lean_nat_dec_lt(x_568, x_569);
if (x_573 == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
lean_dec(x_569);
lean_dec(x_568);
lean_dec_ref(x_567);
lean_dec(x_558);
lean_dec_ref(x_557);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_556)) {
 x_574 = lean_alloc_ctor(0, 2, 0);
} else {
 x_574 = x_556;
}
lean_ctor_set(x_574, 0, x_572);
lean_ctor_set(x_574, 1, x_555);
if (lean_is_scalar(x_554)) {
 x_575 = lean_alloc_ctor(0, 2, 0);
} else {
 x_575 = x_554;
}
lean_ctor_set(x_575, 0, x_553);
lean_ctor_set(x_575, 1, x_574);
if (lean_is_scalar(x_552)) {
 x_576 = lean_alloc_ctor(0, 2, 0);
} else {
 x_576 = x_552;
}
lean_ctor_set(x_576, 0, x_551);
lean_ctor_set(x_576, 1, x_575);
x_577 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_577, 0, x_550);
lean_ctor_set(x_577, 1, x_576);
lean_ctor_set(x_8, 1, x_577);
x_578 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_578, 0, x_8);
lean_ctor_set(x_578, 1, x_14);
return x_578;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; uint8_t x_585; 
if (lean_is_exclusive(x_553)) {
 lean_ctor_release(x_553, 0);
 lean_ctor_release(x_553, 1);
 lean_ctor_release(x_553, 2);
 x_579 = x_553;
} else {
 lean_dec_ref(x_553);
 x_579 = lean_box(0);
}
x_580 = lean_ctor_get(x_551, 0);
lean_inc_ref(x_580);
x_581 = lean_ctor_get(x_551, 1);
lean_inc(x_581);
x_582 = lean_ctor_get(x_551, 2);
lean_inc(x_582);
x_583 = lean_nat_add(x_568, x_570);
lean_inc_ref(x_567);
if (lean_is_scalar(x_579)) {
 x_584 = lean_alloc_ctor(0, 3, 0);
} else {
 x_584 = x_579;
}
lean_ctor_set(x_584, 0, x_567);
lean_ctor_set(x_584, 1, x_583);
lean_ctor_set(x_584, 2, x_569);
x_585 = lean_nat_dec_lt(x_581, x_582);
if (x_585 == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
lean_dec(x_582);
lean_dec(x_581);
lean_dec_ref(x_580);
lean_dec(x_568);
lean_dec_ref(x_567);
lean_dec(x_558);
lean_dec_ref(x_557);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_556)) {
 x_586 = lean_alloc_ctor(0, 2, 0);
} else {
 x_586 = x_556;
}
lean_ctor_set(x_586, 0, x_572);
lean_ctor_set(x_586, 1, x_555);
if (lean_is_scalar(x_554)) {
 x_587 = lean_alloc_ctor(0, 2, 0);
} else {
 x_587 = x_554;
}
lean_ctor_set(x_587, 0, x_584);
lean_ctor_set(x_587, 1, x_586);
if (lean_is_scalar(x_552)) {
 x_588 = lean_alloc_ctor(0, 2, 0);
} else {
 x_588 = x_552;
}
lean_ctor_set(x_588, 0, x_551);
lean_ctor_set(x_588, 1, x_587);
x_589 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_589, 0, x_550);
lean_ctor_set(x_589, 1, x_588);
lean_ctor_set(x_8, 1, x_589);
x_590 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_590, 0, x_8);
lean_ctor_set(x_590, 1, x_14);
return x_590;
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; uint8_t x_597; 
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 lean_ctor_release(x_551, 1);
 lean_ctor_release(x_551, 2);
 x_591 = x_551;
} else {
 lean_dec_ref(x_551);
 x_591 = lean_box(0);
}
x_592 = lean_ctor_get(x_550, 0);
lean_inc_ref(x_592);
x_593 = lean_ctor_get(x_550, 1);
lean_inc(x_593);
x_594 = lean_ctor_get(x_550, 2);
lean_inc(x_594);
x_595 = lean_nat_add(x_581, x_570);
lean_inc_ref(x_580);
if (lean_is_scalar(x_591)) {
 x_596 = lean_alloc_ctor(0, 3, 0);
} else {
 x_596 = x_591;
}
lean_ctor_set(x_596, 0, x_580);
lean_ctor_set(x_596, 1, x_595);
lean_ctor_set(x_596, 2, x_582);
x_597 = lean_nat_dec_lt(x_593, x_594);
if (x_597 == 0)
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
lean_dec(x_594);
lean_dec(x_593);
lean_dec_ref(x_592);
lean_dec(x_581);
lean_dec_ref(x_580);
lean_dec(x_568);
lean_dec_ref(x_567);
lean_dec(x_558);
lean_dec_ref(x_557);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_556)) {
 x_598 = lean_alloc_ctor(0, 2, 0);
} else {
 x_598 = x_556;
}
lean_ctor_set(x_598, 0, x_572);
lean_ctor_set(x_598, 1, x_555);
if (lean_is_scalar(x_554)) {
 x_599 = lean_alloc_ctor(0, 2, 0);
} else {
 x_599 = x_554;
}
lean_ctor_set(x_599, 0, x_584);
lean_ctor_set(x_599, 1, x_598);
if (lean_is_scalar(x_552)) {
 x_600 = lean_alloc_ctor(0, 2, 0);
} else {
 x_600 = x_552;
}
lean_ctor_set(x_600, 0, x_596);
lean_ctor_set(x_600, 1, x_599);
x_601 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_601, 0, x_550);
lean_ctor_set(x_601, 1, x_600);
lean_ctor_set(x_8, 1, x_601);
x_602 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_602, 0, x_8);
lean_ctor_set(x_602, 1, x_14);
return x_602;
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; uint8_t x_609; 
if (lean_is_exclusive(x_550)) {
 lean_ctor_release(x_550, 0);
 lean_ctor_release(x_550, 1);
 lean_ctor_release(x_550, 2);
 x_603 = x_550;
} else {
 lean_dec_ref(x_550);
 x_603 = lean_box(0);
}
x_604 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_604);
x_605 = lean_ctor_get(x_21, 1);
lean_inc(x_605);
x_606 = lean_ctor_get(x_21, 2);
lean_inc(x_606);
x_607 = lean_nat_add(x_593, x_570);
lean_inc_ref(x_592);
if (lean_is_scalar(x_603)) {
 x_608 = lean_alloc_ctor(0, 3, 0);
} else {
 x_608 = x_603;
}
lean_ctor_set(x_608, 0, x_592);
lean_ctor_set(x_608, 1, x_607);
lean_ctor_set(x_608, 2, x_594);
x_609 = lean_nat_dec_lt(x_605, x_606);
if (x_609 == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
lean_dec(x_606);
lean_dec(x_605);
lean_dec_ref(x_604);
lean_dec(x_593);
lean_dec_ref(x_592);
lean_dec(x_581);
lean_dec_ref(x_580);
lean_dec(x_568);
lean_dec_ref(x_567);
lean_dec(x_558);
lean_dec_ref(x_557);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_556)) {
 x_610 = lean_alloc_ctor(0, 2, 0);
} else {
 x_610 = x_556;
}
lean_ctor_set(x_610, 0, x_572);
lean_ctor_set(x_610, 1, x_555);
if (lean_is_scalar(x_554)) {
 x_611 = lean_alloc_ctor(0, 2, 0);
} else {
 x_611 = x_554;
}
lean_ctor_set(x_611, 0, x_584);
lean_ctor_set(x_611, 1, x_610);
if (lean_is_scalar(x_552)) {
 x_612 = lean_alloc_ctor(0, 2, 0);
} else {
 x_612 = x_552;
}
lean_ctor_set(x_612, 0, x_596);
lean_ctor_set(x_612, 1, x_611);
x_613 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_613, 0, x_608);
lean_ctor_set(x_613, 1, x_612);
lean_ctor_set(x_8, 1, x_613);
x_614 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_614, 0, x_8);
lean_ctor_set(x_614, 1, x_14);
return x_614;
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_615 = x_21;
} else {
 lean_dec_ref(x_21);
 x_615 = lean_box(0);
}
x_616 = lean_array_fget(x_557, x_558);
lean_dec(x_558);
lean_dec_ref(x_557);
x_617 = lean_array_fget(x_567, x_568);
lean_dec(x_568);
lean_dec_ref(x_567);
x_618 = lean_array_fget(x_580, x_581);
lean_dec(x_581);
lean_dec_ref(x_580);
x_619 = lean_array_fget(x_592, x_593);
lean_dec(x_593);
lean_dec_ref(x_592);
x_620 = lean_array_fget(x_604, x_605);
x_621 = lean_box(x_2);
x_622 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_623 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_623, 0, x_616);
lean_closure_set(x_623, 1, x_1);
lean_closure_set(x_623, 2, x_9);
lean_closure_set(x_623, 3, x_621);
lean_closure_set(x_623, 4, x_622);
lean_closure_set(x_623, 5, x_620);
lean_closure_set(x_623, 6, x_4);
lean_closure_set(x_623, 7, x_5);
lean_closure_set(x_623, 8, x_618);
x_624 = lean_nat_sub(x_619, x_5);
lean_dec(x_619);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_6);
x_625 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg(x_617, x_624, x_6, x_623, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_625) == 0)
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; uint8_t x_637; 
x_626 = lean_ctor_get(x_625, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_625, 1);
lean_inc(x_627);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 x_628 = x_625;
} else {
 lean_dec_ref(x_625);
 x_628 = lean_box(0);
}
x_629 = lean_nat_add(x_605, x_570);
lean_dec(x_605);
if (lean_is_scalar(x_615)) {
 x_630 = lean_alloc_ctor(0, 3, 0);
} else {
 x_630 = x_615;
}
lean_ctor_set(x_630, 0, x_604);
lean_ctor_set(x_630, 1, x_629);
lean_ctor_set(x_630, 2, x_606);
x_631 = lean_array_push(x_555, x_626);
if (lean_is_scalar(x_556)) {
 x_632 = lean_alloc_ctor(0, 2, 0);
} else {
 x_632 = x_556;
}
lean_ctor_set(x_632, 0, x_572);
lean_ctor_set(x_632, 1, x_631);
if (lean_is_scalar(x_554)) {
 x_633 = lean_alloc_ctor(0, 2, 0);
} else {
 x_633 = x_554;
}
lean_ctor_set(x_633, 0, x_584);
lean_ctor_set(x_633, 1, x_632);
if (lean_is_scalar(x_552)) {
 x_634 = lean_alloc_ctor(0, 2, 0);
} else {
 x_634 = x_552;
}
lean_ctor_set(x_634, 0, x_596);
lean_ctor_set(x_634, 1, x_633);
x_635 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_635, 0, x_608);
lean_ctor_set(x_635, 1, x_634);
lean_ctor_set(x_8, 1, x_635);
lean_ctor_set(x_8, 0, x_630);
x_636 = lean_nat_add(x_9, x_570);
lean_dec(x_9);
x_637 = lean_nat_dec_lt(x_636, x_7);
if (x_637 == 0)
{
lean_object* x_638; 
lean_dec(x_636);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_628)) {
 x_638 = lean_alloc_ctor(0, 2, 0);
} else {
 x_638 = x_628;
}
lean_ctor_set(x_638, 0, x_8);
lean_ctor_set(x_638, 1, x_627);
return x_638;
}
else
{
lean_dec(x_628);
x_9 = x_636;
x_14 = x_627;
goto _start;
}
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_615);
lean_dec_ref(x_608);
lean_dec(x_606);
lean_dec(x_605);
lean_dec_ref(x_604);
lean_dec_ref(x_596);
lean_dec_ref(x_584);
lean_dec_ref(x_572);
lean_dec(x_556);
lean_dec(x_555);
lean_dec(x_554);
lean_dec(x_552);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_640 = lean_ctor_get(x_625, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_625, 1);
lean_inc(x_641);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 x_642 = x_625;
} else {
 lean_dec_ref(x_625);
 x_642 = lean_box(0);
}
if (lean_is_scalar(x_642)) {
 x_643 = lean_alloc_ctor(1, 2, 0);
} else {
 x_643 = x_642;
}
lean_ctor_set(x_643, 0, x_640);
lean_ctor_set(x_643, 1, x_641);
return x_643;
}
}
}
}
}
}
}
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; uint8_t x_656; 
x_644 = lean_ctor_get(x_8, 0);
lean_inc(x_644);
lean_dec(x_8);
x_645 = lean_ctor_get(x_15, 0);
lean_inc(x_645);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_646 = x_15;
} else {
 lean_dec_ref(x_15);
 x_646 = lean_box(0);
}
x_647 = lean_ctor_get(x_16, 0);
lean_inc(x_647);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_648 = x_16;
} else {
 lean_dec_ref(x_16);
 x_648 = lean_box(0);
}
x_649 = lean_ctor_get(x_17, 0);
lean_inc(x_649);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_650 = x_17;
} else {
 lean_dec_ref(x_17);
 x_650 = lean_box(0);
}
x_651 = lean_ctor_get(x_18, 1);
lean_inc(x_651);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_652 = x_18;
} else {
 lean_dec_ref(x_18);
 x_652 = lean_box(0);
}
x_653 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_653);
x_654 = lean_ctor_get(x_19, 1);
lean_inc(x_654);
x_655 = lean_ctor_get(x_19, 2);
lean_inc(x_655);
x_656 = lean_nat_dec_lt(x_654, x_655);
if (x_656 == 0)
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; 
lean_dec(x_655);
lean_dec(x_654);
lean_dec_ref(x_653);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_652)) {
 x_657 = lean_alloc_ctor(0, 2, 0);
} else {
 x_657 = x_652;
}
lean_ctor_set(x_657, 0, x_19);
lean_ctor_set(x_657, 1, x_651);
if (lean_is_scalar(x_650)) {
 x_658 = lean_alloc_ctor(0, 2, 0);
} else {
 x_658 = x_650;
}
lean_ctor_set(x_658, 0, x_649);
lean_ctor_set(x_658, 1, x_657);
if (lean_is_scalar(x_648)) {
 x_659 = lean_alloc_ctor(0, 2, 0);
} else {
 x_659 = x_648;
}
lean_ctor_set(x_659, 0, x_647);
lean_ctor_set(x_659, 1, x_658);
if (lean_is_scalar(x_646)) {
 x_660 = lean_alloc_ctor(0, 2, 0);
} else {
 x_660 = x_646;
}
lean_ctor_set(x_660, 0, x_645);
lean_ctor_set(x_660, 1, x_659);
x_661 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_661, 0, x_644);
lean_ctor_set(x_661, 1, x_660);
x_662 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_662, 0, x_661);
lean_ctor_set(x_662, 1, x_14);
return x_662;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; uint8_t x_670; 
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_663 = x_19;
} else {
 lean_dec_ref(x_19);
 x_663 = lean_box(0);
}
x_664 = lean_ctor_get(x_649, 0);
lean_inc_ref(x_664);
x_665 = lean_ctor_get(x_649, 1);
lean_inc(x_665);
x_666 = lean_ctor_get(x_649, 2);
lean_inc(x_666);
x_667 = lean_unsigned_to_nat(1u);
x_668 = lean_nat_add(x_654, x_667);
lean_inc_ref(x_653);
if (lean_is_scalar(x_663)) {
 x_669 = lean_alloc_ctor(0, 3, 0);
} else {
 x_669 = x_663;
}
lean_ctor_set(x_669, 0, x_653);
lean_ctor_set(x_669, 1, x_668);
lean_ctor_set(x_669, 2, x_655);
x_670 = lean_nat_dec_lt(x_665, x_666);
if (x_670 == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
lean_dec(x_666);
lean_dec(x_665);
lean_dec_ref(x_664);
lean_dec(x_654);
lean_dec_ref(x_653);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_652)) {
 x_671 = lean_alloc_ctor(0, 2, 0);
} else {
 x_671 = x_652;
}
lean_ctor_set(x_671, 0, x_669);
lean_ctor_set(x_671, 1, x_651);
if (lean_is_scalar(x_650)) {
 x_672 = lean_alloc_ctor(0, 2, 0);
} else {
 x_672 = x_650;
}
lean_ctor_set(x_672, 0, x_649);
lean_ctor_set(x_672, 1, x_671);
if (lean_is_scalar(x_648)) {
 x_673 = lean_alloc_ctor(0, 2, 0);
} else {
 x_673 = x_648;
}
lean_ctor_set(x_673, 0, x_647);
lean_ctor_set(x_673, 1, x_672);
if (lean_is_scalar(x_646)) {
 x_674 = lean_alloc_ctor(0, 2, 0);
} else {
 x_674 = x_646;
}
lean_ctor_set(x_674, 0, x_645);
lean_ctor_set(x_674, 1, x_673);
x_675 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_675, 0, x_644);
lean_ctor_set(x_675, 1, x_674);
x_676 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_676, 0, x_675);
lean_ctor_set(x_676, 1, x_14);
return x_676;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; uint8_t x_683; 
if (lean_is_exclusive(x_649)) {
 lean_ctor_release(x_649, 0);
 lean_ctor_release(x_649, 1);
 lean_ctor_release(x_649, 2);
 x_677 = x_649;
} else {
 lean_dec_ref(x_649);
 x_677 = lean_box(0);
}
x_678 = lean_ctor_get(x_647, 0);
lean_inc_ref(x_678);
x_679 = lean_ctor_get(x_647, 1);
lean_inc(x_679);
x_680 = lean_ctor_get(x_647, 2);
lean_inc(x_680);
x_681 = lean_nat_add(x_665, x_667);
lean_inc_ref(x_664);
if (lean_is_scalar(x_677)) {
 x_682 = lean_alloc_ctor(0, 3, 0);
} else {
 x_682 = x_677;
}
lean_ctor_set(x_682, 0, x_664);
lean_ctor_set(x_682, 1, x_681);
lean_ctor_set(x_682, 2, x_666);
x_683 = lean_nat_dec_lt(x_679, x_680);
if (x_683 == 0)
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
lean_dec(x_680);
lean_dec(x_679);
lean_dec_ref(x_678);
lean_dec(x_665);
lean_dec_ref(x_664);
lean_dec(x_654);
lean_dec_ref(x_653);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_652)) {
 x_684 = lean_alloc_ctor(0, 2, 0);
} else {
 x_684 = x_652;
}
lean_ctor_set(x_684, 0, x_669);
lean_ctor_set(x_684, 1, x_651);
if (lean_is_scalar(x_650)) {
 x_685 = lean_alloc_ctor(0, 2, 0);
} else {
 x_685 = x_650;
}
lean_ctor_set(x_685, 0, x_682);
lean_ctor_set(x_685, 1, x_684);
if (lean_is_scalar(x_648)) {
 x_686 = lean_alloc_ctor(0, 2, 0);
} else {
 x_686 = x_648;
}
lean_ctor_set(x_686, 0, x_647);
lean_ctor_set(x_686, 1, x_685);
if (lean_is_scalar(x_646)) {
 x_687 = lean_alloc_ctor(0, 2, 0);
} else {
 x_687 = x_646;
}
lean_ctor_set(x_687, 0, x_645);
lean_ctor_set(x_687, 1, x_686);
x_688 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_688, 0, x_644);
lean_ctor_set(x_688, 1, x_687);
x_689 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_689, 0, x_688);
lean_ctor_set(x_689, 1, x_14);
return x_689;
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; uint8_t x_696; 
if (lean_is_exclusive(x_647)) {
 lean_ctor_release(x_647, 0);
 lean_ctor_release(x_647, 1);
 lean_ctor_release(x_647, 2);
 x_690 = x_647;
} else {
 lean_dec_ref(x_647);
 x_690 = lean_box(0);
}
x_691 = lean_ctor_get(x_645, 0);
lean_inc_ref(x_691);
x_692 = lean_ctor_get(x_645, 1);
lean_inc(x_692);
x_693 = lean_ctor_get(x_645, 2);
lean_inc(x_693);
x_694 = lean_nat_add(x_679, x_667);
lean_inc_ref(x_678);
if (lean_is_scalar(x_690)) {
 x_695 = lean_alloc_ctor(0, 3, 0);
} else {
 x_695 = x_690;
}
lean_ctor_set(x_695, 0, x_678);
lean_ctor_set(x_695, 1, x_694);
lean_ctor_set(x_695, 2, x_680);
x_696 = lean_nat_dec_lt(x_692, x_693);
if (x_696 == 0)
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
lean_dec(x_693);
lean_dec(x_692);
lean_dec_ref(x_691);
lean_dec(x_679);
lean_dec_ref(x_678);
lean_dec(x_665);
lean_dec_ref(x_664);
lean_dec(x_654);
lean_dec_ref(x_653);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_652)) {
 x_697 = lean_alloc_ctor(0, 2, 0);
} else {
 x_697 = x_652;
}
lean_ctor_set(x_697, 0, x_669);
lean_ctor_set(x_697, 1, x_651);
if (lean_is_scalar(x_650)) {
 x_698 = lean_alloc_ctor(0, 2, 0);
} else {
 x_698 = x_650;
}
lean_ctor_set(x_698, 0, x_682);
lean_ctor_set(x_698, 1, x_697);
if (lean_is_scalar(x_648)) {
 x_699 = lean_alloc_ctor(0, 2, 0);
} else {
 x_699 = x_648;
}
lean_ctor_set(x_699, 0, x_695);
lean_ctor_set(x_699, 1, x_698);
if (lean_is_scalar(x_646)) {
 x_700 = lean_alloc_ctor(0, 2, 0);
} else {
 x_700 = x_646;
}
lean_ctor_set(x_700, 0, x_645);
lean_ctor_set(x_700, 1, x_699);
x_701 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_701, 0, x_644);
lean_ctor_set(x_701, 1, x_700);
x_702 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_702, 0, x_701);
lean_ctor_set(x_702, 1, x_14);
return x_702;
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; uint8_t x_709; 
if (lean_is_exclusive(x_645)) {
 lean_ctor_release(x_645, 0);
 lean_ctor_release(x_645, 1);
 lean_ctor_release(x_645, 2);
 x_703 = x_645;
} else {
 lean_dec_ref(x_645);
 x_703 = lean_box(0);
}
x_704 = lean_ctor_get(x_644, 0);
lean_inc_ref(x_704);
x_705 = lean_ctor_get(x_644, 1);
lean_inc(x_705);
x_706 = lean_ctor_get(x_644, 2);
lean_inc(x_706);
x_707 = lean_nat_add(x_692, x_667);
lean_inc_ref(x_691);
if (lean_is_scalar(x_703)) {
 x_708 = lean_alloc_ctor(0, 3, 0);
} else {
 x_708 = x_703;
}
lean_ctor_set(x_708, 0, x_691);
lean_ctor_set(x_708, 1, x_707);
lean_ctor_set(x_708, 2, x_693);
x_709 = lean_nat_dec_lt(x_705, x_706);
if (x_709 == 0)
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
lean_dec(x_706);
lean_dec(x_705);
lean_dec_ref(x_704);
lean_dec(x_692);
lean_dec_ref(x_691);
lean_dec(x_679);
lean_dec_ref(x_678);
lean_dec(x_665);
lean_dec_ref(x_664);
lean_dec(x_654);
lean_dec_ref(x_653);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_652)) {
 x_710 = lean_alloc_ctor(0, 2, 0);
} else {
 x_710 = x_652;
}
lean_ctor_set(x_710, 0, x_669);
lean_ctor_set(x_710, 1, x_651);
if (lean_is_scalar(x_650)) {
 x_711 = lean_alloc_ctor(0, 2, 0);
} else {
 x_711 = x_650;
}
lean_ctor_set(x_711, 0, x_682);
lean_ctor_set(x_711, 1, x_710);
if (lean_is_scalar(x_648)) {
 x_712 = lean_alloc_ctor(0, 2, 0);
} else {
 x_712 = x_648;
}
lean_ctor_set(x_712, 0, x_695);
lean_ctor_set(x_712, 1, x_711);
if (lean_is_scalar(x_646)) {
 x_713 = lean_alloc_ctor(0, 2, 0);
} else {
 x_713 = x_646;
}
lean_ctor_set(x_713, 0, x_708);
lean_ctor_set(x_713, 1, x_712);
x_714 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_714, 0, x_644);
lean_ctor_set(x_714, 1, x_713);
x_715 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_715, 0, x_714);
lean_ctor_set(x_715, 1, x_14);
return x_715;
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
if (lean_is_exclusive(x_644)) {
 lean_ctor_release(x_644, 0);
 lean_ctor_release(x_644, 1);
 lean_ctor_release(x_644, 2);
 x_716 = x_644;
} else {
 lean_dec_ref(x_644);
 x_716 = lean_box(0);
}
x_717 = lean_array_fget(x_653, x_654);
lean_dec(x_654);
lean_dec_ref(x_653);
x_718 = lean_array_fget(x_664, x_665);
lean_dec(x_665);
lean_dec_ref(x_664);
x_719 = lean_array_fget(x_678, x_679);
lean_dec(x_679);
lean_dec_ref(x_678);
x_720 = lean_array_fget(x_691, x_692);
lean_dec(x_692);
lean_dec_ref(x_691);
x_721 = lean_array_fget(x_704, x_705);
x_722 = lean_box(x_2);
x_723 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_724 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_724, 0, x_717);
lean_closure_set(x_724, 1, x_1);
lean_closure_set(x_724, 2, x_9);
lean_closure_set(x_724, 3, x_722);
lean_closure_set(x_724, 4, x_723);
lean_closure_set(x_724, 5, x_721);
lean_closure_set(x_724, 6, x_4);
lean_closure_set(x_724, 7, x_5);
lean_closure_set(x_724, 8, x_719);
x_725 = lean_nat_sub(x_720, x_5);
lean_dec(x_720);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_6);
x_726 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg(x_718, x_725, x_6, x_724, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_726) == 0)
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; uint8_t x_739; 
x_727 = lean_ctor_get(x_726, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_726, 1);
lean_inc(x_728);
if (lean_is_exclusive(x_726)) {
 lean_ctor_release(x_726, 0);
 lean_ctor_release(x_726, 1);
 x_729 = x_726;
} else {
 lean_dec_ref(x_726);
 x_729 = lean_box(0);
}
x_730 = lean_nat_add(x_705, x_667);
lean_dec(x_705);
if (lean_is_scalar(x_716)) {
 x_731 = lean_alloc_ctor(0, 3, 0);
} else {
 x_731 = x_716;
}
lean_ctor_set(x_731, 0, x_704);
lean_ctor_set(x_731, 1, x_730);
lean_ctor_set(x_731, 2, x_706);
x_732 = lean_array_push(x_651, x_727);
if (lean_is_scalar(x_652)) {
 x_733 = lean_alloc_ctor(0, 2, 0);
} else {
 x_733 = x_652;
}
lean_ctor_set(x_733, 0, x_669);
lean_ctor_set(x_733, 1, x_732);
if (lean_is_scalar(x_650)) {
 x_734 = lean_alloc_ctor(0, 2, 0);
} else {
 x_734 = x_650;
}
lean_ctor_set(x_734, 0, x_682);
lean_ctor_set(x_734, 1, x_733);
if (lean_is_scalar(x_648)) {
 x_735 = lean_alloc_ctor(0, 2, 0);
} else {
 x_735 = x_648;
}
lean_ctor_set(x_735, 0, x_695);
lean_ctor_set(x_735, 1, x_734);
if (lean_is_scalar(x_646)) {
 x_736 = lean_alloc_ctor(0, 2, 0);
} else {
 x_736 = x_646;
}
lean_ctor_set(x_736, 0, x_708);
lean_ctor_set(x_736, 1, x_735);
x_737 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_737, 0, x_731);
lean_ctor_set(x_737, 1, x_736);
x_738 = lean_nat_add(x_9, x_667);
lean_dec(x_9);
x_739 = lean_nat_dec_lt(x_738, x_7);
if (x_739 == 0)
{
lean_object* x_740; 
lean_dec(x_738);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_729)) {
 x_740 = lean_alloc_ctor(0, 2, 0);
} else {
 x_740 = x_729;
}
lean_ctor_set(x_740, 0, x_737);
lean_ctor_set(x_740, 1, x_728);
return x_740;
}
else
{
lean_dec(x_729);
x_8 = x_737;
x_9 = x_738;
x_14 = x_728;
goto _start;
}
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
lean_dec(x_716);
lean_dec_ref(x_708);
lean_dec(x_706);
lean_dec(x_705);
lean_dec_ref(x_704);
lean_dec_ref(x_695);
lean_dec_ref(x_682);
lean_dec_ref(x_669);
lean_dec(x_652);
lean_dec(x_651);
lean_dec(x_650);
lean_dec(x_648);
lean_dec(x_646);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_742 = lean_ctor_get(x_726, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_726, 1);
lean_inc(x_743);
if (lean_is_exclusive(x_726)) {
 lean_ctor_release(x_726, 0);
 lean_ctor_release(x_726, 1);
 x_744 = x_726;
} else {
 lean_dec_ref(x_726);
 x_744 = lean_box(0);
}
if (lean_is_scalar(x_744)) {
 x_745 = lean_alloc_ctor(1, 2, 0);
} else {
 x_745 = x_744;
}
lean_ctor_set(x_745, 0, x_742);
lean_ctor_set(x_745, 1, x_743);
return x_745;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; 
x_22 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_13, x_14, x_17, x_18, x_19, x_20, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_array_size(x_1);
x_9 = 0;
x_10 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__5___redArg(x_8, x_9, x_1, x_3, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
x_14 = lean_apply_7(x_1, x_2, x_3, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Meta_MatcherApp_transform___redArg___lam__20___closed__0;
x_19 = lean_array_get_size(x_4);
x_20 = l_Array_toSubarray___redArg(x_4, x_17, x_19);
x_21 = lean_array_get_size(x_5);
x_22 = l_Array_toSubarray___redArg(x_5, x_17, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_array_size(x_2);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_27 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__7(x_6, x_2, x_26, x_7, x_25, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_29, 1);
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec_ref(x_27);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
x_37 = 0;
x_38 = 1;
x_39 = 1;
lean_inc(x_36);
x_40 = l_Lean_Meta_mkLambdaFVars(x_2, x_36, x_37, x_38, x_37, x_38, x_39, x_9, x_10, x_11, x_12, x_33);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = l_Lean_Meta_getLevel(x_36, x_9, x_10, x_11, x_12, x_42);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_ctor_set(x_31, 1, x_35);
lean_ctor_set(x_31, 0, x_45);
lean_ctor_set(x_29, 0, x_41);
lean_ctor_set(x_43, 0, x_29);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_43);
lean_ctor_set(x_31, 1, x_35);
lean_ctor_set(x_31, 0, x_46);
lean_ctor_set(x_29, 0, x_41);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_29);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_41);
lean_free_object(x_31);
lean_dec(x_35);
lean_free_object(x_29);
x_49 = !lean_is_exclusive(x_43);
if (x_49 == 0)
{
return x_43;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_43, 0);
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_43);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_free_object(x_31);
lean_dec(x_36);
lean_dec(x_35);
lean_free_object(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_53 = !lean_is_exclusive(x_40);
if (x_53 == 0)
{
return x_40;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_40, 0);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_40);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_31, 0);
x_58 = lean_ctor_get(x_31, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_31);
x_59 = 0;
x_60 = 1;
x_61 = 1;
lean_inc(x_58);
x_62 = l_Lean_Meta_mkLambdaFVars(x_2, x_58, x_59, x_60, x_59, x_60, x_61, x_9, x_10, x_11, x_12, x_33);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec_ref(x_62);
x_65 = l_Lean_Meta_getLevel(x_58, x_9, x_10, x_11, x_12, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_57);
lean_ctor_set(x_29, 1, x_69);
lean_ctor_set(x_29, 0, x_63);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_29);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_63);
lean_dec(x_57);
lean_free_object(x_29);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_29);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_75 = lean_ctor_get(x_62, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_62, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_77 = x_62;
} else {
 lean_dec_ref(x_62);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; lean_object* x_87; 
x_79 = lean_ctor_get(x_29, 1);
lean_inc(x_79);
lean_dec(x_29);
x_80 = lean_ctor_get(x_27, 1);
lean_inc(x_80);
lean_dec_ref(x_27);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_83 = x_79;
} else {
 lean_dec_ref(x_79);
 x_83 = lean_box(0);
}
x_84 = 0;
x_85 = 1;
x_86 = 1;
lean_inc(x_82);
x_87 = l_Lean_Meta_mkLambdaFVars(x_2, x_82, x_84, x_85, x_84, x_85, x_86, x_9, x_10, x_11, x_12, x_80);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec_ref(x_87);
x_90 = l_Lean_Meta_getLevel(x_82, x_9, x_10, x_11, x_12, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_83;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_81);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_94);
if (lean_is_scalar(x_93)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_93;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_92);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_88);
lean_dec(x_83);
lean_dec(x_81);
x_97 = lean_ctor_get(x_90, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_90, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_99 = x_90;
} else {
 lean_dec_ref(x_90);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_101 = lean_ctor_get(x_87, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_87, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_103 = x_87;
} else {
 lean_dec_ref(x_87);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_105 = !lean_is_exclusive(x_27);
if (x_105 == 0)
{
return x_27;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_27, 0);
x_107 = lean_ctor_get(x_27, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_27);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_109 = !lean_is_exclusive(x_14);
if (x_109 == 0)
{
return x_14;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_14, 0);
x_111 = lean_ctor_get(x_14, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_14);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_array_get_size(x_7);
x_15 = lean_array_get_size(x_6);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_17 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4;
x_18 = l_Nat_reprFast(x_15);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_MessageData_ofFormat(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_23, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_15);
x_29 = lean_box(0);
x_30 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__1(x_1, x_7, x_8, x_2, x_3, x_4, x_5, x_29, x_9, x_10, x_11, x_12, x_13);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_14, 1);
x_21 = lean_ctor_get(x_20, 1);
x_22 = lean_ctor_get(x_21, 1);
x_23 = lean_apply_6(x_1, x_2, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_Array_append___redArg(x_3, x_25);
lean_dec(x_25);
x_27 = lean_array_size(x_4);
x_28 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9(x_5, x_27, x_6, x_4);
lean_inc(x_22);
x_29 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_8);
lean_ctor_set(x_29, 2, x_9);
lean_ctor_set(x_29, 3, x_10);
lean_ctor_set(x_29, 4, x_11);
lean_ctor_set(x_29, 5, x_12);
lean_ctor_set(x_29, 6, x_13);
lean_ctor_set(x_29, 7, x_28);
lean_ctor_set(x_29, 8, x_22);
lean_ctor_set(x_29, 9, x_26);
lean_ctor_set(x_23, 0, x_29);
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = l_Array_append___redArg(x_3, x_30);
lean_dec(x_30);
x_33 = lean_array_size(x_4);
x_34 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9(x_5, x_33, x_6, x_4);
lean_inc(x_22);
x_35 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_35, 0, x_7);
lean_ctor_set(x_35, 1, x_8);
lean_ctor_set(x_35, 2, x_9);
lean_ctor_set(x_35, 3, x_10);
lean_ctor_set(x_35, 4, x_11);
lean_ctor_set(x_35, 5, x_12);
lean_ctor_set(x_35, 6, x_13);
lean_ctor_set(x_35, 7, x_34);
lean_ctor_set(x_35, 8, x_22);
lean_ctor_set(x_35, 9, x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, uint8_t x_18, lean_object* x_19, uint8_t x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27) {
_start:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_array_get_size(x_1);
lean_inc(x_26);
lean_inc_ref(x_25);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_28);
x_29 = l_Lean_Meta_inferArgumentTypesN(x_28, x_2, x_23, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
lean_inc(x_28);
lean_inc(x_15);
x_32 = l_Array_toSubarray___redArg(x_1, x_15, x_28);
x_33 = lean_array_get_size(x_5);
lean_inc(x_15);
lean_inc_ref(x_5);
x_34 = l_Array_toSubarray___redArg(x_5, x_15, x_33);
x_35 = lean_array_get_size(x_30);
lean_inc(x_15);
x_36 = l_Array_toSubarray___redArg(x_30, x_15, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_16);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_nat_dec_lt(x_15, x_28);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
x_41 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__3(x_3, x_4, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_39, x_23, x_24, x_25, x_26, x_31);
lean_dec_ref(x_39);
lean_dec(x_6);
return x_41;
}
else
{
lean_object* x_42; 
lean_inc(x_26);
lean_inc_ref(x_25);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_6);
x_42 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg(x_17, x_18, x_19, x_20, x_6, x_28, x_39, x_15, x_23, x_24, x_25, x_26, x_31);
lean_dec(x_28);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__3(x_3, x_4, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_43, x_23, x_24, x_25, x_26, x_44);
lean_dec(x_43);
lean_dec(x_6);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_50 = !lean_is_exclusive(x_29);
if (x_50 == 0)
{
return x_29;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_29, 0);
x_52 = lean_ctor_get(x_29, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_29);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_14, 1);
x_21 = lean_ctor_get(x_20, 1);
x_22 = lean_ctor_get(x_21, 1);
x_23 = lean_ctor_get(x_22, 1);
x_24 = lean_ctor_get(x_23, 1);
x_25 = lean_apply_6(x_1, x_2, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = l_Array_append___redArg(x_3, x_27);
lean_dec(x_27);
x_29 = lean_array_size(x_4);
x_30 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9(x_5, x_29, x_6, x_4);
lean_inc(x_24);
x_31 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_31, 0, x_7);
lean_ctor_set(x_31, 1, x_8);
lean_ctor_set(x_31, 2, x_9);
lean_ctor_set(x_31, 3, x_10);
lean_ctor_set(x_31, 4, x_11);
lean_ctor_set(x_31, 5, x_12);
lean_ctor_set(x_31, 6, x_13);
lean_ctor_set(x_31, 7, x_30);
lean_ctor_set(x_31, 8, x_24);
lean_ctor_set(x_31, 9, x_28);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = l_Array_append___redArg(x_3, x_32);
lean_dec(x_32);
x_35 = lean_array_size(x_4);
x_36 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9(x_5, x_35, x_6, x_4);
lean_inc(x_24);
x_37 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_8);
lean_ctor_set(x_37, 2, x_9);
lean_ctor_set(x_37, 3, x_10);
lean_ctor_set(x_37, 4, x_11);
lean_ctor_set(x_37, 5, x_12);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_36);
lean_ctor_set(x_37, 8, x_24);
lean_ctor_set(x_37, 9, x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_39 = !lean_is_exclusive(x_25);
if (x_39 == 0)
{
return x_25;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_25, 0);
x_41 = lean_ctor_get(x_25, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_25);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, uint8_t x_21, uint8_t x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30) {
_start:
{
lean_object* x_31; 
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_1);
x_31 = l_Lean_Meta_inferArgumentTypesN(x_1, x_2, x_26, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
lean_inc(x_1);
lean_inc(x_16);
x_34 = l_Array_toSubarray___redArg(x_15, x_16, x_1);
x_35 = lean_array_get_size(x_17);
lean_inc(x_16);
x_36 = l_Array_toSubarray___redArg(x_17, x_16, x_35);
x_37 = lean_array_get_size(x_5);
lean_inc(x_16);
lean_inc_ref(x_5);
x_38 = l_Array_toSubarray___redArg(x_5, x_16, x_37);
x_39 = lean_array_get_size(x_18);
lean_inc(x_16);
x_40 = l_Array_toSubarray___redArg(x_18, x_16, x_39);
x_41 = lean_array_get_size(x_32);
lean_inc(x_16);
x_42 = l_Array_toSubarray___redArg(x_32, x_16, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_19);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_nat_dec_lt(x_16, x_1);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_1);
x_49 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5(x_3, x_4, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_47, x_26, x_27, x_28, x_29, x_33);
lean_dec_ref(x_47);
lean_dec(x_6);
return x_49;
}
else
{
lean_object* x_50; 
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_16);
lean_inc(x_6);
x_50 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg(x_20, x_21, x_22, x_6, x_23, x_16, x_1, x_47, x_16, x_26, x_27, x_28, x_29, x_33);
lean_dec(x_1);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5(x_3, x_4, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_51, x_26, x_27, x_28, x_29, x_52);
lean_dec(x_51);
lean_dec(x_6);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_50);
if (x_54 == 0)
{
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_50, 0);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_50);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_31);
if (x_58 == 0)
{
return x_31;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_31, 0);
x_60 = lean_ctor_get(x_31, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_31);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, size_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, uint8_t x_19, uint8_t x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28) {
_start:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_array_get_size(x_1);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_29);
x_30 = l_Lean_Meta_inferArgumentTypesN(x_29, x_2, x_24, x_25, x_26, x_27, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
x_33 = lean_get_match_equations_for(x_3, x_24, x_25, x_26, x_27, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 2);
lean_inc_ref(x_37);
lean_dec(x_34);
lean_inc(x_36);
x_38 = l_Lean_Expr_const___override(x_36, x_4);
x_39 = l_Lean_mkAppN(x_38, x_5);
lean_inc_ref(x_6);
x_40 = l_Lean_Expr_app___override(x_39, x_6);
x_41 = l_Lean_mkAppN(x_40, x_7);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc_ref(x_41);
x_42 = l_Lean_Meta_isTypeCorrect(x_41, x_24, x_25, x_26, x_27, x_35);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec_ref(x_42);
x_46 = l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__1;
lean_inc_ref(x_41);
x_47 = l_Lean_indentExpr(x_41);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(x_51, 0, x_50);
lean_inc_ref(x_41);
x_52 = lean_alloc_closure((void*)(l_Lean_Meta_check), 6, 1);
lean_closure_set(x_52, 0, x_41);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
x_53 = l_Lean_Meta_mapErrorImp___redArg(x_52, x_51, x_24, x_25, x_26, x_27, x_45);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__6(x_29, x_41, x_8, x_9, x_37, x_10, x_11, x_36, x_12, x_13, x_14, x_5, x_6, x_7, x_1, x_15, x_16, x_31, x_17, x_18, x_19, x_20, x_21, x_22, x_54, x_24, x_25, x_26, x_27, x_55);
lean_dec(x_54);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec_ref(x_41);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 0);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_53);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_42, 1);
lean_inc(x_61);
lean_dec_ref(x_42);
x_62 = lean_box(0);
x_63 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__6(x_29, x_41, x_8, x_9, x_37, x_10, x_11, x_36, x_12, x_13, x_14, x_5, x_6, x_7, x_1, x_15, x_16, x_31, x_17, x_18, x_19, x_20, x_21, x_22, x_62, x_24, x_25, x_26, x_27, x_61);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec_ref(x_41);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_64 = !lean_is_exclusive(x_42);
if (x_64 == 0)
{
return x_42;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_42, 0);
x_66 = lean_ctor_get(x_42, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_42);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_68 = !lean_is_exclusive(x_33);
if (x_68 == 0)
{
return x_33;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_33, 0);
x_70 = lean_ctor_get(x_33, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_33);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_72 = !lean_is_exclusive(x_30);
if (x_72 == 0)
{
return x_30;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_30, 0);
x_74 = lean_ctor_get(x_30, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_30);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__9(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, uint8_t x_16, uint8_t x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24) {
_start:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__0;
x_27 = l_Array_reverse___redArg(x_1);
x_28 = lean_array_get_size(x_27);
x_29 = l_Array_toSubarray___redArg(x_27, x_25, x_28);
lean_inc_ref(x_2);
x_30 = l_Array_reverse___redArg(x_2);
x_31 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__1;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_array_size(x_30);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
x_34 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__8(x_30, x_33, x_3, x_32, x_20, x_21, x_22, x_23, x_24);
lean_dec_ref(x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec_ref(x_34);
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_41 = x_36;
} else {
 lean_dec_ref(x_36);
 x_41 = lean_box(0);
}
if (x_16 == 0)
{
lean_dec(x_18);
goto block_73;
}
else
{
if (x_17 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_13);
lean_inc_ref(x_19);
x_74 = lean_array_to_list(x_19);
lean_inc(x_74);
lean_inc(x_4);
x_75 = l_Lean_Expr_const___override(x_4, x_74);
x_76 = l_Lean_mkAppN(x_75, x_5);
lean_inc_ref(x_6);
x_77 = l_Lean_Expr_app___override(x_76, x_6);
x_78 = l_Lean_mkAppN(x_77, x_2);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc_ref(x_78);
x_79 = l_Lean_Meta_isTypeCorrect(x_78, x_20, x_21, x_22, x_23, x_38);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec_ref(x_79);
x_83 = l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__1;
lean_inc_ref(x_78);
x_84 = l_Lean_indentExpr(x_78);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3;
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(x_88, 0, x_87);
lean_inc_ref(x_78);
x_89 = lean_alloc_closure((void*)(l_Lean_Meta_check), 6, 1);
lean_closure_set(x_89, 0, x_78);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
x_90 = l_Lean_Meta_mapErrorImp___redArg(x_89, x_88, x_20, x_21, x_22, x_23, x_82);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec_ref(x_90);
x_93 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__8(x_7, x_78, x_4, x_74, x_5, x_6, x_2, x_8, x_9, x_39, x_3, x_19, x_11, x_12, x_25, x_10, x_26, x_15, x_14, x_16, x_18, x_40, x_91, x_20, x_21, x_22, x_23, x_92);
lean_dec(x_91);
return x_93;
}
else
{
uint8_t x_94; 
lean_dec_ref(x_78);
lean_dec(x_74);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_94 = !lean_is_exclusive(x_90);
if (x_94 == 0)
{
return x_90;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_90, 0);
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_90);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_79, 1);
lean_inc(x_98);
lean_dec_ref(x_79);
x_99 = lean_box(0);
x_100 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__8(x_7, x_78, x_4, x_74, x_5, x_6, x_2, x_8, x_9, x_39, x_3, x_19, x_11, x_12, x_25, x_10, x_26, x_15, x_14, x_16, x_18, x_40, x_99, x_20, x_21, x_22, x_23, x_98);
return x_100;
}
}
else
{
uint8_t x_101; 
lean_dec_ref(x_78);
lean_dec(x_74);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_101 = !lean_is_exclusive(x_79);
if (x_101 == 0)
{
return x_79;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_79, 0);
x_103 = lean_ctor_get(x_79, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_79);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_dec(x_18);
goto block_73;
}
}
block_73:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_inc_ref(x_19);
x_42 = lean_array_to_list(x_19);
lean_inc(x_4);
x_43 = l_Lean_Expr_const___override(x_4, x_42);
x_44 = l_Lean_mkAppN(x_43, x_5);
lean_inc_ref(x_6);
x_45 = l_Lean_Expr_app___override(x_44, x_6);
x_46 = l_Lean_mkAppN(x_45, x_2);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc_ref(x_46);
x_47 = l_Lean_Meta_isTypeCorrect(x_46, x_20, x_21, x_22, x_23, x_38);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = 1;
x_51 = lean_unbox(x_48);
lean_dec(x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__1;
lean_inc_ref(x_46);
x_53 = l_Lean_indentExpr(x_46);
if (lean_is_scalar(x_41)) {
 x_54 = lean_alloc_ctor(7, 2, 0);
} else {
 x_54 = x_41;
 lean_ctor_set_tag(x_54, 7);
}
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3;
if (lean_is_scalar(x_37)) {
 x_56 = lean_alloc_ctor(7, 2, 0);
} else {
 x_56 = x_37;
 lean_ctor_set_tag(x_56, 7);
}
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_inc_ref(x_22);
x_57 = l_Lean_logError___at___Lean_inferDefEqAttr_spec__1(x_56, x_20, x_21, x_22, x_23, x_49);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec_ref(x_57);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc_ref(x_46);
x_59 = l_Lean_Meta_check(x_46, x_20, x_21, x_22, x_23, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
x_62 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__4(x_7, x_46, x_8, x_9, x_10, x_39, x_3, x_4, x_19, x_11, x_12, x_5, x_6, x_2, x_25, x_26, x_13, x_14, x_15, x_50, x_40, x_60, x_20, x_21, x_22, x_23, x_61);
lean_dec(x_60);
return x_62;
}
else
{
uint8_t x_63; 
lean_dec_ref(x_46);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_63 = !lean_is_exclusive(x_59);
if (x_63 == 0)
{
return x_59;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_59, 0);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_59);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_41);
lean_dec(x_37);
x_67 = lean_box(0);
x_68 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__4(x_7, x_46, x_8, x_9, x_10, x_39, x_3, x_4, x_19, x_11, x_12, x_5, x_6, x_2, x_25, x_26, x_13, x_14, x_15, x_50, x_40, x_67, x_20, x_21, x_22, x_23, x_49);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec_ref(x_46);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_69 = !lean_is_exclusive(x_47);
if (x_69 == 0)
{
return x_47;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_47, 0);
x_71 = lean_ctor_get(x_47, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_47);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_105 = !lean_is_exclusive(x_34);
if (x_105 == 0)
{
return x_34;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_34, 0);
x_107 = lean_ctor_get(x_34, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_34);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, uint8_t x_16, uint8_t x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24) {
_start:
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = lean_array_size(x_1);
x_26 = 0;
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_2);
x_27 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__6(x_2, x_25, x_26, x_1, x_20, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = lean_array_size(x_3);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc_ref(x_3);
x_31 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__6(x_2, x_30, x_26, x_3, x_20, x_21, x_22, x_23, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = lean_box(x_6);
x_35 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7___boxed__const__1;
lean_inc_ref(x_5);
lean_inc(x_32);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__2___boxed), 13, 6);
lean_closure_set(x_36, 0, x_4);
lean_closure_set(x_36, 1, x_32);
lean_closure_set(x_36, 2, x_5);
lean_closure_set(x_36, 3, x_34);
lean_closure_set(x_36, 4, x_35);
lean_closure_set(x_36, 5, x_3);
x_37 = 0;
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
x_38 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_7, x_36, x_37, x_20, x_21, x_22, x_23, x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec_ref(x_38);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__9(x_43, x_32, x_26, x_8, x_28, x_42, x_9, x_10, x_11, x_12, x_13, x_5, x_14, x_37, x_15, x_16, x_17, x_19, x_18, x_20, x_21, x_22, x_23, x_41);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec_ref(x_38);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_dec(x_40);
x_49 = lean_ctor_get(x_13, 0);
lean_inc(x_49);
x_50 = lean_array_set(x_18, x_49, x_47);
lean_dec(x_49);
x_51 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__9(x_48, x_32, x_26, x_8, x_28, x_46, x_9, x_10, x_11, x_12, x_13, x_5, x_14, x_37, x_15, x_16, x_17, x_19, x_50, x_20, x_21, x_22, x_23, x_45);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_5);
x_52 = !lean_is_exclusive(x_38);
if (x_52 == 0)
{
return x_38;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_38, 0);
x_54 = lean_ctor_get(x_38, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_38);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_28);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_56 = !lean_is_exclusive(x_31);
if (x_56 == 0)
{
return x_31;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_31, 0);
x_58 = lean_ctor_get(x_31, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_31);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_27);
if (x_60 == 0)
{
return x_27;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_27, 0);
x_62 = lean_ctor_get(x_27, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_27);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_ref_get(x_11, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_1, 8);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_1, 9);
lean_inc_ref(x_27);
lean_dec_ref(x_1);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__0___boxed), 7, 0);
lean_inc(x_18);
x_29 = l_Lean_isCasesOnRecursor(x_17, x_18);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_inc(x_18);
x_30 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(x_18, x_11, x_16);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_30, 1);
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
x_35 = l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__1;
x_36 = l_Lean_MessageData_ofName(x_18);
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_36);
lean_ctor_set(x_30, 0, x_35);
x_37 = l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__3;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_37);
lean_ctor_set(x_13, 0, x_30);
x_38 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_13, x_8, x_9, x_10, x_11, x_33);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_30, 1);
lean_inc(x_43);
lean_dec(x_30);
x_44 = l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__1;
x_45 = l_Lean_MessageData_ofName(x_18);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__3;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_47);
lean_ctor_set(x_13, 0, x_46);
x_48 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_13, x_8, x_9, x_10, x_11, x_43);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_free_object(x_13);
x_53 = lean_ctor_get(x_30, 1);
lean_inc(x_53);
lean_dec_ref(x_30);
x_54 = lean_ctor_get(x_31, 0);
lean_inc(x_54);
lean_dec(x_31);
x_55 = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(x_54);
lean_dec(x_54);
x_56 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7(x_22, x_4, x_24, x_5, x_21, x_3, x_23, x_18, x_26, x_7, x_27, x_25, x_20, x_28, x_6, x_2, x_29, x_19, x_55, x_8, x_9, x_10, x_11, x_53);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_free_object(x_13);
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7(x_22, x_4, x_24, x_5, x_21, x_3, x_23, x_18, x_26, x_7, x_27, x_25, x_20, x_28, x_6, x_2, x_29, x_19, x_57, x_8, x_9, x_10, x_11, x_16);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_59 = lean_ctor_get(x_13, 0);
x_60 = lean_ctor_get(x_13, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_13);
x_61 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_1, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_1, 8);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_1, 9);
lean_inc_ref(x_71);
lean_dec_ref(x_1);
x_72 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__0___boxed), 7, 0);
lean_inc(x_62);
x_73 = l_Lean_isCasesOnRecursor(x_61, x_62);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_inc(x_62);
x_74 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(x_62, x_11, x_60);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec_ref(x_72);
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec_ref(x_69);
lean_dec_ref(x_68);
lean_dec_ref(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
x_78 = l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__1;
x_79 = l_Lean_MessageData_ofName(x_62);
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(7, 2, 0);
} else {
 x_80 = x_77;
 lean_ctor_set_tag(x_80, 7);
}
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__3;
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_82, x_8, x_9, x_10, x_11, x_76);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_74, 1);
lean_inc(x_88);
lean_dec_ref(x_74);
x_89 = lean_ctor_get(x_75, 0);
lean_inc(x_89);
lean_dec(x_75);
x_90 = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(x_89);
lean_dec(x_89);
x_91 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7(x_66, x_4, x_68, x_5, x_65, x_3, x_67, x_62, x_70, x_7, x_71, x_69, x_64, x_72, x_6, x_2, x_73, x_63, x_90, x_8, x_9, x_10, x_11, x_88);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_unsigned_to_nat(0u);
x_93 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7(x_66, x_4, x_68, x_5, x_65, x_3, x_67, x_62, x_70, x_7, x_71, x_69, x_64, x_72, x_6, x_2, x_73, x_63, x_92, x_8, x_9, x_10, x_11, x_60);
return x_93;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot close goal after splitting: ", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_10 = lean_infer_type(x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_13 = l_Lean_Meta_mkEq(x_3, x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_box(0);
lean_inc_ref(x_5);
x_17 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_14, x_16, x_5, x_6, x_7, x_8, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_29 = l_Lean_Expr_mvarId_x21(x_18);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_30 = l_Lean_Meta_Split_simpMatchTarget(x_29, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_31);
x_33 = l_Lean_MVarId_refl(x_31, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_dec(x_31);
lean_dec(x_20);
x_21 = x_33;
goto block_28;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_56; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
x_56 = l_Lean_Exception_isInterrupt(x_34);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = l_Lean_Exception_isRuntime(x_34);
lean_dec(x_34);
x_36 = x_57;
goto block_55;
}
else
{
lean_dec(x_34);
x_36 = x_56;
goto block_55;
}
block_55:
{
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_33, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_33, 0);
lean_dec(x_39);
x_40 = l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1;
lean_inc(x_31);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set_tag(x_33, 7);
lean_ctor_set(x_33, 1, x_41);
lean_ctor_set(x_33, 0, x_40);
x_42 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3;
if (lean_is_scalar(x_20)) {
 x_43 = lean_alloc_ctor(7, 2, 0);
} else {
 x_43 = x_20;
 lean_ctor_set_tag(x_43, 7);
}
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_42);
lean_inc_ref(x_7);
x_44 = l_Lean_logInfo___at___Lean_Meta_reportDiag_spec__0(x_43, x_5, x_6, x_7, x_8, x_35);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_46 = l_Lean_MVarId_admit(x_31, x_1, x_5, x_6, x_7, x_8, x_45);
x_21 = x_46;
goto block_28;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_33);
x_47 = l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1;
lean_inc(x_31);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_31);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3;
if (lean_is_scalar(x_20)) {
 x_51 = lean_alloc_ctor(7, 2, 0);
} else {
 x_51 = x_20;
 lean_ctor_set_tag(x_51, 7);
}
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_inc_ref(x_7);
x_52 = l_Lean_logInfo___at___Lean_Meta_reportDiag_spec__0(x_51, x_5, x_6, x_7, x_8, x_35);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec_ref(x_52);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_54 = l_Lean_MVarId_admit(x_31, x_1, x_5, x_6, x_7, x_8, x_53);
x_21 = x_54;
goto block_28;
}
}
else
{
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_20);
x_21 = x_33;
goto block_28;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_58 = !lean_is_exclusive(x_30);
if (x_58 == 0)
{
return x_30;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_30, 0);
x_60 = lean_ctor_get(x_30, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_30);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
block_28:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Lean_Meta_mkEqMPR(x_18, x_4, x_5, x_6, x_7, x_8, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; 
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_1);
x_22 = l_Lean_Meta_arrowDomainsN(x_1, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0;
x_26 = 1;
lean_inc_ref(x_15);
x_27 = l_Lean_Meta_mkLambdaFVars(x_15, x_25, x_2, x_3, x_2, x_3, x_26, x_17, x_18, x_19, x_20, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = lean_array_size(x_4);
x_31 = 0;
lean_inc(x_20);
lean_inc_ref(x_19);
x_32 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3(x_1, x_5, x_6, x_7, x_8, x_2, x_3, x_26, x_30, x_31, x_4, x_17, x_18, x_19, x_20, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
if (lean_obj_tag(x_10) == 0)
{
x_35 = x_14;
x_36 = x_19;
x_37 = x_20;
goto block_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_10, 0);
lean_inc(x_43);
x_44 = l_Lean_levelOne;
x_45 = lean_array_set(x_14, x_43, x_44);
lean_dec(x_43);
x_35 = x_45;
x_36 = x_19;
x_37 = x_20;
goto block_42;
}
block_42:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__0;
x_39 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_39, 0, x_9);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_10);
lean_ctor_set(x_39, 3, x_11);
lean_ctor_set(x_39, 4, x_12);
lean_ctor_set(x_39, 5, x_28);
lean_ctor_set(x_39, 6, x_15);
lean_ctor_set(x_39, 7, x_13);
lean_ctor_set(x_39, 8, x_33);
lean_ctor_set(x_39, 9, x_38);
x_40 = l_Lean_Meta_MatcherApp_toExpr(x_39);
x_41 = l_Lean_mkArrowN(x_23, x_40, x_36, x_37, x_34);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_23);
return x_41;
}
}
else
{
uint8_t x_46; 
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_46 = !lean_is_exclusive(x_32);
if (x_46 == 0)
{
return x_32;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_32, 0);
x_48 = lean_ctor_get(x_32, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_32);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_27;
}
}
else
{
uint8_t x_50; 
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_22);
if (x_50 == 0)
{
return x_22;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_22, 0);
x_52 = lean_ctor_get(x_22, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_22);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 8);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 9);
lean_inc_ref(x_14);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed), 6, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed), 2, 0);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__5___boxed), 6, 0);
x_18 = lean_array_get_size(x_14);
lean_dec_ref(x_14);
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed), 9, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_box(x_19);
lean_inc_ref_n(x_16, 3);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed), 21, 14);
lean_closure_set(x_25, 0, x_18);
lean_closure_set(x_25, 1, x_23);
lean_closure_set(x_25, 2, x_24);
lean_closure_set(x_25, 3, x_13);
lean_closure_set(x_25, 4, x_16);
lean_closure_set(x_25, 5, x_16);
lean_closure_set(x_25, 6, x_16);
lean_closure_set(x_25, 7, x_16);
lean_closure_set(x_25, 8, x_7);
lean_closure_set(x_25, 9, x_9);
lean_closure_set(x_25, 10, x_10);
lean_closure_set(x_25, 11, x_11);
lean_closure_set(x_25, 12, x_12);
lean_closure_set(x_25, 13, x_8);
x_26 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5(x_1, x_19, x_22, x_15, x_25, x_21, x_17, x_2, x_3, x_4, x_5, x_6);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_4);
x_16 = lean_unbox(x_5);
x_17 = lean_unbox(x_6);
x_18 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1(x_1, x_2, x_3, x_15, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_15 = lean_unbox(x_4);
x_16 = lean_unbox(x_5);
x_17 = lean_unbox(x_6);
x_18 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_19 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_20 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg(x_1, x_2, x_3, x_15, x_16, x_17, x_18, x_19, x_9, x_10, x_11, x_12, x_13, x_14);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_17 = lean_unbox(x_6);
x_18 = lean_unbox(x_7);
x_19 = lean_unbox(x_8);
x_20 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_21 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_22 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_19, x_20, x_21, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_17 = lean_unbox(x_6);
x_18 = lean_unbox(x_7);
x_19 = lean_unbox(x_8);
x_20 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_21 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_22 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_19, x_20, x_21, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__5___redArg(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__5(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__6(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__7(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__8(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_7);
x_15 = lean_unbox(x_8);
x_16 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_14, x_15, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_3);
x_16 = lean_unbox(x_7);
x_17 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__1(x_1, x_2, x_15, x_4, x_5, x_6, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_3);
x_16 = lean_unbox(x_6);
x_17 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2(x_1, x_2, x_15, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
x_15 = lean_unbox(x_4);
x_16 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg(x_1, x_14, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_21 = lean_unbox(x_2);
x_22 = lean_unbox(x_4);
x_23 = lean_unbox(x_6);
x_24 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11(x_1, x_21, x_3, x_22, x_5, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_11);
lean_dec(x_10);
return x_24;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_6);
x_18 = lean_unbox(x_7);
x_19 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_5);
x_18 = lean_unbox(x_6);
x_19 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__1(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_4);
x_18 = lean_unbox(x_5);
x_19 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__2(x_1, x_2, x_3, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_4);
x_18 = lean_unbox(x_5);
x_19 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3(x_1, x_2, x_3, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_2);
x_16 = lean_unbox(x_3);
x_17 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_unbox(x_2);
x_23 = lean_unbox(x_3);
x_24 = lean_unbox(x_7);
x_25 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13(x_1, x_22, x_23, x_4, x_5, x_6, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_12);
lean_dec(x_11);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__1(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__2(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
size_t x_20; lean_object* x_21; 
x_20 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_21 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__3(x_1, x_2, x_3, x_4, x_5, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec_ref(x_14);
lean_dec(x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__4___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
_start:
{
size_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; 
x_28 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_29 = lean_unbox(x_18);
x_30 = lean_unbox(x_20);
x_31 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_28, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_29, x_19, x_30, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
size_t x_20; lean_object* x_21; 
x_20 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_21 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5(x_1, x_2, x_3, x_4, x_5, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec_ref(x_14);
lean_dec(x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__6___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
_start:
{
size_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_32 = lean_unbox(x_21);
x_33 = lean_unbox(x_22);
x_34 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_31, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_32, x_33, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
return x_34;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__8___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
_start:
{
size_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; 
x_29 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_30 = lean_unbox(x_19);
x_31 = lean_unbox(x_20);
x_32 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_30, x_31, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
return x_32;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__9___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
_start:
{
size_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_26 = lean_unbox(x_14);
x_27 = lean_unbox(x_16);
x_28 = lean_unbox(x_17);
x_29 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__9(x_1, x_2, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_26, x_15, x_27, x_28, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
_start:
{
uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_25 = lean_unbox(x_6);
x_26 = lean_unbox(x_16);
x_27 = lean_unbox(x_17);
x_28 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7(x_1, x_2, x_3, x_4, x_5, x_25, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_26, x_27, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
x_14 = lean_unbox(x_3);
x_15 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_MatcherApp_inferMatchType___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_MatcherApp_inferMatchType___lam__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_MatcherApp_inferMatchType___lam__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Lean_Meta_MatcherApp_inferMatchType___lam__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_unbox(x_2);
x_23 = lean_unbox(x_3);
x_24 = l_Lean_Meta_MatcherApp_inferMatchType___lam__3(x_1, x_22, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_6);
lean_dec(x_5);
return x_24;
}
}
lean_object* initialize_Lean_Meta_Match(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Match(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Split(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0 = _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0);
l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1 = _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1);
l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2 = _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0 = _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0);
l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1 = _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1);
l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__2 = _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__2);
l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3 = _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3);
l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0 = _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0);
l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1 = _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1);
l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2 = _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2);
l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3 = _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4 = _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4);
l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5 = _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6 = _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__6);
l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___closed__0 = _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___closed__0();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___closed__0);
l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___closed__1 = _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___closed__1);
l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0 = _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0);
l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1 = _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1);
l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2 = _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2);
l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3 = _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3();
lean_mark_persistent(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3);
l_Lean_Meta_MatcherApp_transform___redArg___lam__20___closed__0 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__20___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__20___closed__0);
l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__0 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__0);
l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__1 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__1);
l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__2 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__2);
l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__3 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__3();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__3);
l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__4 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__4();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__4);
l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__5 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__5();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__5);
l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__6 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__6();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__6);
l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__7 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__7();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__7);
l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__8 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__8();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__8);
l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__9 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__9();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__25___closed__9);
l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__0 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__0);
l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__1 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__1);
l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__0 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__0);
l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__1 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__1);
l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__2 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__2);
l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___closed__3);
l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__0 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__0);
l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__1 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__1);
l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__2 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__2);
l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3);
l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__0 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__0);
l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__1 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__1);
l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__0 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__0);
l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__1 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__62___closed__1);
l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__0 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__0);
l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__1 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__1);
l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__2 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__2);
l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__3 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__3();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__71___closed__3);
l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__0 = _init_l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__0();
lean_mark_persistent(l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__0);
l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__1 = _init_l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__1();
lean_mark_persistent(l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__1);
l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__2 = _init_l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__2();
lean_mark_persistent(l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__2);
l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__3 = _init_l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__3();
lean_mark_persistent(l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__3);
l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__4 = _init_l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__4();
lean_mark_persistent(l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__4);
l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__5 = _init_l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__5();
lean_mark_persistent(l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___redArg___closed__5);
l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1___closed__0 = _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1___closed__0();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1___closed__0);
l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1___closed__1 = _init_l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___redArg___lam__1___closed__1);
l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7___boxed__const__1 = _init_l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7___boxed__const__1);
l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0 = _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0);
l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1 = _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1);
l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0 = _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
