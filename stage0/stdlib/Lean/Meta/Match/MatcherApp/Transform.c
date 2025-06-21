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
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__3;
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1(uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logInfo___at___Lean_Meta_reportDiag_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__69___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__6___boxed(lean_object**);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__5___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__1;
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRev___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7___boxed(lean_object**);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62___boxed(lean_object**);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMPR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_arrowDomainsN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__7(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__7;
lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_arrowDomainsN_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__66(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__6;
static lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_admit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5___boxed(lean_object**);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__3___boxed(lean_object**);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed(lean_object**);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__1___closed__3;
lean_object* l_Lean_Meta_Match_getEquationsFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1;
lean_object* l_Array_ofSubarray___redArg(lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logError___at___Lean_inferDefEqAttr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrowN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3(lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__1___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Split_simpMatchTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__69(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx_x27___at_____private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___Lean_Meta_introNCore_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__70___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__67(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__5;
lean_object* l_Array_forIn_x27Unsafe_loop___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__70(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__5;
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__66___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed(lean_object**);
extern lean_object* l_Lean_levelOne;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1(uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__1;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__0;
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__3;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed(lean_object**);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_box(0);
x_14 = lean_box(1);
x_15 = lean_unbox(x_13);
x_16 = lean_unbox(x_13);
x_17 = lean_unbox(x_14);
lean_inc(x_6);
x_18 = l_Lean_Meta_mkLambdaFVars(x_6, x_1, x_15, x_2, x_16, x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
if (x_4 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = l_Lean_instInhabitedExpr;
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_array_get(x_45, x_6, x_46);
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_48 = lean_infer_type(x_47, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_51 = l_Lean_Meta_isExprDefEq(x_5, x_49, x_8, x_9, x_10, x_11, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_21 = x_2;
x_22 = x_8;
x_23 = x_9;
x_24 = x_10;
x_25 = x_11;
x_26 = x_54;
goto block_44;
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_21 = x_4;
x_22 = x_8;
x_23 = x_9;
x_24 = x_10;
x_25 = x_11;
x_26 = x_55;
goto block_44;
}
}
else
{
uint8_t x_56; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_51);
if (x_56 == 0)
{
return x_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_51, 0);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_51);
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
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_48);
if (x_60 == 0)
{
return x_48;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_48, 0);
x_62 = lean_ctor_get(x_48, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_48);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
x_21 = x_4;
x_22 = x_8;
x_23 = x_9;
x_24 = x_10;
x_25 = x_11;
x_26 = x_20;
goto block_44;
}
block_44:
{
uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; 
x_27 = lean_unbox(x_13);
x_28 = lean_unbox(x_13);
x_29 = lean_unbox(x_14);
x_30 = l_Lean_Meta_mkLambdaFVars(x_3, x_19, x_27, x_2, x_28, x_29, x_22, x_23, x_24, x_25, x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_box(x_21);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_30);
x_37 = lean_box(x_21);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
return x_30;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_30, 0);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_30);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_18);
if (x_64 == 0)
{
return x_18;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_18, 0);
x_66 = lean_ctor_get(x_18, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_18);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
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
lean_object* x_12; lean_object* x_27; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_27 = l_Lean_Meta_instantiateLambda(x_4, x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_27) == 0)
{
x_12 = x_27;
goto block_26;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_34; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
x_34 = l_Lean_Exception_isInterrupt(x_28);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Exception_isRuntime(x_28);
lean_dec(x_28);
x_30 = x_35;
goto block_33;
}
else
{
lean_dec(x_28);
x_30 = x_34;
goto block_33;
}
block_33:
{
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_27);
x_31 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2;
x_32 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_31, x_7, x_8, x_9, x_10, x_29);
x_12 = x_32;
goto block_26;
}
else
{
lean_dec(x_29);
x_12 = x_27;
goto block_26;
}
}
}
block_26:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(x_1);
x_16 = lean_box(x_2);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed), 12, 5);
lean_closure_set(x_17, 0, x_13);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_5);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_3);
x_18 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0;
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_6, x_18, x_17, x_20, x_7, x_8, x_9, x_10, x_14);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
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
lean_dec(x_2);
lean_dec(x_1);
if (x_5 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_14 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1;
x_15 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l_Lean_Meta_whnfD(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 7)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 2);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = lean_array_fget(x_4, x_6);
x_25 = lean_box(x_13);
x_26 = lean_box(x_5);
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed), 11, 4);
lean_closure_set(x_27, 0, x_25);
lean_closure_set(x_27, 1, x_26);
lean_closure_set(x_27, 2, x_1);
lean_closure_set(x_27, 3, x_24);
x_28 = lean_array_get(x_23, x_3, x_6);
lean_inc(x_28);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_32 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_21, x_29, x_27, x_31, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_expr_instantiate1(x_22, x_35);
lean_dec(x_22);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_28, x_38);
lean_dec(x_28);
x_40 = lean_array_set(x_3, x_6, x_39);
x_41 = lean_array_fset(x_4, x_6, x_35);
x_42 = lean_nat_add(x_6, x_38);
lean_dec(x_6);
x_43 = lean_unbox(x_36);
lean_dec(x_36);
x_2 = x_37;
x_3 = x_40;
x_4 = x_41;
x_5 = x_43;
x_6 = x_42;
x_11 = x_34;
goto _start;
}
else
{
uint8_t x_45; 
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_32);
if (x_45 == 0)
{
return x_32;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_32, 0);
x_47 = lean_ctor_get(x_32, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_32);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = lean_ctor_get(x_18, 1);
lean_inc(x_49);
lean_dec(x_18);
x_50 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3;
x_51 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_50, x_7, x_8, x_9, x_10, x_49);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_18);
if (x_52 == 0)
{
return x_18;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_18, 0);
x_54 = lean_ctor_get(x_18, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_18);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
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
lean_dec(x_2);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(x_1, x_13, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_3);
x_7 = l_Lean_Expr_isFVar(x_6);
if (x_7 == 0)
{
lean_dec(x_6);
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_instInhabitedExpr;
x_9 = lean_array_get(x_8, x_2, x_3);
x_10 = l_Lean_Expr_replaceFVar(x_5, x_6, x_9);
lean_dec(x_9);
return x_10;
}
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to add argument to matcher application, type error when constructing the new motive", 90, 90);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_addArg___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected matcher application, motive must be lambda expression with #", 71, 71);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_addArg___lam__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" arguments", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_addArg___lam__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_array_get_size(x_11);
x_101 = lean_array_get_size(x_2);
x_102 = lean_nat_dec_eq(x_100, x_101);
lean_dec(x_100);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = l_Lean_Meta_MatcherApp_addArg___lam__1___closed__4;
x_104 = l_Nat_reprFast(x_101);
x_105 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_Lean_MessageData_ofFormat(x_105);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_Meta_MatcherApp_addArg___lam__1___closed__6;
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_109, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
return x_110;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_110, 0);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_110);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
else
{
lean_object* x_115; 
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
x_115 = lean_infer_type(x_1, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
lean_inc(x_11);
lean_inc(x_2);
x_118 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_addArg___lam__0___boxed), 5, 2);
lean_closure_set(x_118, 0, x_2);
lean_closure_set(x_118, 1, x_11);
lean_inc(x_116);
x_119 = l_Nat_foldRev___redArg(x_101, x_118, x_116);
x_120 = l_Lean_mkArrow___redArg(x_119, x_12, x_16, x_117);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_18 = x_116;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_3;
x_24 = x_2;
x_25 = x_8;
x_26 = x_121;
x_27 = x_9;
x_28 = x_10;
x_29 = x_13;
x_30 = x_14;
x_31 = x_15;
x_32 = x_16;
x_33 = x_122;
goto block_99;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_120, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
lean_dec(x_120);
x_125 = lean_ctor_get(x_3, 0);
lean_inc(x_125);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_123);
x_126 = l_Lean_Meta_getLevel(x_123, x_13, x_14, x_15, x_16, x_124);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_array_set(x_10, x_125, x_127);
lean_dec(x_125);
x_18 = x_116;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_3;
x_24 = x_2;
x_25 = x_8;
x_26 = x_123;
x_27 = x_9;
x_28 = x_129;
x_29 = x_13;
x_30 = x_14;
x_31 = x_15;
x_32 = x_16;
x_33 = x_128;
goto block_99;
}
else
{
uint8_t x_130; 
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_116);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_126);
if (x_130 == 0)
{
return x_126;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_126, 0);
x_132 = lean_ctor_get(x_126, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_126);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_101);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_134 = !lean_is_exclusive(x_115);
if (x_134 == 0)
{
return x_115;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_115, 0);
x_136 = lean_ctor_get(x_115, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_115);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
block_99:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; 
x_34 = lean_box(0);
x_35 = lean_box(1);
x_36 = lean_box(1);
x_37 = lean_unbox(x_34);
x_38 = lean_unbox(x_35);
x_39 = lean_unbox(x_34);
x_40 = lean_unbox(x_36);
x_41 = l_Lean_Meta_mkLambdaFVars(x_11, x_26, x_37, x_38, x_39, x_40, x_29, x_30, x_31, x_32, x_33);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_28);
x_44 = lean_array_to_list(x_28);
lean_inc(x_20);
x_45 = l_Lean_Expr_const___override(x_20, x_44);
x_46 = l_Lean_mkAppN(x_45, x_22);
lean_inc(x_42);
x_47 = l_Lean_Expr_app___override(x_46, x_42);
x_48 = l_Lean_mkAppN(x_47, x_24);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_48);
x_49 = l_Lean_Meta_isTypeCorrect(x_48, x_29, x_30, x_31, x_32, x_43);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_48);
lean_dec(x_42);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_1);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l_Lean_Meta_MatcherApp_addArg___lam__1___closed__1;
x_54 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_53, x_29, x_30, x_31, x_32, x_52);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
return x_54;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_54);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_49, 1);
lean_inc(x_59);
lean_dec(x_49);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_60 = lean_infer_type(x_48, x_29, x_30, x_31, x_32, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_unbox(x_34);
x_65 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(x_18, x_61, x_25, x_27, x_64, x_63, x_29, x_30, x_31, x_32, x_62);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Meta_MatcherApp_addArg___lam__1___closed__2;
x_71 = lean_array_push(x_70, x_1);
x_72 = l_Array_append___redArg(x_71, x_21);
x_73 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_73, 0, x_20);
lean_ctor_set(x_73, 1, x_28);
lean_ctor_set(x_73, 2, x_23);
lean_ctor_set(x_73, 3, x_19);
lean_ctor_set(x_73, 4, x_22);
lean_ctor_set(x_73, 5, x_42);
lean_ctor_set(x_73, 6, x_24);
lean_ctor_set(x_73, 7, x_68);
lean_ctor_set(x_73, 8, x_69);
lean_ctor_set(x_73, 9, x_72);
lean_ctor_set(x_65, 0, x_73);
return x_65;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_74 = lean_ctor_get(x_65, 0);
x_75 = lean_ctor_get(x_65, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_65);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = l_Lean_Meta_MatcherApp_addArg___lam__1___closed__2;
x_79 = lean_array_push(x_78, x_1);
x_80 = l_Array_append___redArg(x_79, x_21);
x_81 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_81, 0, x_20);
lean_ctor_set(x_81, 1, x_28);
lean_ctor_set(x_81, 2, x_23);
lean_ctor_set(x_81, 3, x_19);
lean_ctor_set(x_81, 4, x_22);
lean_ctor_set(x_81, 5, x_42);
lean_ctor_set(x_81, 6, x_24);
lean_ctor_set(x_81, 7, x_76);
lean_ctor_set(x_81, 8, x_77);
lean_ctor_set(x_81, 9, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_75);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_42);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_65);
if (x_83 == 0)
{
return x_65;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_65, 0);
x_85 = lean_ctor_get(x_65, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_65);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_42);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_60);
if (x_87 == 0)
{
return x_60;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_60, 0);
x_89 = lean_ctor_get(x_60, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_60);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_48);
lean_dec(x_42);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_49);
if (x_91 == 0)
{
return x_49;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_49, 0);
x_93 = lean_ctor_get(x_49, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_49);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_41);
if (x_95 == 0)
{
return x_41;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_41, 0);
x_97 = lean_ctor_get(x_41, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_41);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 7);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 8);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 9);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_addArg___lam__1___boxed), 17, 10);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_14);
lean_closure_set(x_18, 2, x_10);
lean_closure_set(x_18, 3, x_11);
lean_closure_set(x_18, 4, x_8);
lean_closure_set(x_18, 5, x_17);
lean_closure_set(x_18, 6, x_12);
lean_closure_set(x_18, 7, x_15);
lean_closure_set(x_18, 8, x_16);
lean_closure_set(x_18, 9, x_9);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_13, x_18, x_20, x_3, x_4, x_5, x_6, x_7);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_MatcherApp_addArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__1___boxed(lean_object** _args) {
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
x_18 = l_Lean_Meta_MatcherApp_addArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_6);
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
lean_dec(x_8);
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
lean_dec(x_27);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
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
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Meta_kabstract(x_5, x_16, x_17, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_2);
x_21 = lean_array_get(x_2, x_3, x_15);
x_22 = lean_expr_instantiate1(x_19, x_21);
lean_dec(x_21);
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
lean_dec(x_18);
x_4 = x_15;
x_5 = x_24;
x_10 = x_25;
goto _start;
}
else
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
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
lean_dec(x_5);
x_23 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___closed__1;
x_24 = l_Nat_reprFast(x_4);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_MessageData_ofFormat(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Meta_MatcherApp_addArg___lam__1___closed__6;
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
x_19 = l_Lean_Meta_mkLambdaFVars(x_5, x_18, x_1, x_2, x_1, x_3, x_7, x_8, x_9, x_10, x_12);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_16, x_21, x_20, x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_16, x_21, x_20, x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l_Array_mapMUnsafe_map___at___Lean_Meta_arrowDomainsN_spec__2(x_12, x_13, x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Array_zip___redArg(x_1, x_15);
lean_dec(x_15);
x_18 = lean_array_size(x_17);
x_19 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1(x_2, x_3, x_4, x_18, x_13, x_17, x_7, x_8, x_9, x_10, x_16);
return x_19;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_array_get_size(x_9);
x_71 = lean_array_get_size(x_1);
x_72 = lean_nat_dec_eq(x_70, x_71);
lean_dec(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3;
x_74 = l_Nat_reprFast(x_71);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = l_Lean_MessageData_ofFormat(x_75);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Meta_MatcherApp_addArg___lam__1___closed__6;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_79, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
return x_80;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_80);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
else
{
lean_object* x_85; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_85 = l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(x_1, x_2, x_9, x_71, x_3, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_86);
x_88 = l_Lean_Meta_mkEq(x_86, x_86, x_11, x_12, x_13, x_14, x_87);
if (lean_obj_tag(x_88) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_16 = x_90;
x_17 = x_89;
x_18 = x_1;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
x_22 = x_11;
x_23 = x_12;
x_24 = x_13;
x_25 = x_14;
goto block_69;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_88, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_box(0);
x_95 = lean_array_set(x_8, x_93, x_94);
x_16 = x_92;
x_17 = x_91;
x_18 = x_1;
x_19 = x_6;
x_20 = x_7;
x_21 = x_95;
x_22 = x_11;
x_23 = x_12;
x_24 = x_13;
x_25 = x_14;
goto block_69;
}
}
else
{
uint8_t x_96; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_96 = !lean_is_exclusive(x_88);
if (x_96 == 0)
{
return x_88;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_88, 0);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_88);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_100 = !lean_is_exclusive(x_85);
if (x_100 == 0)
{
return x_85;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_85, 0);
x_102 = lean_ctor_get(x_85, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_85);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
block_69:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; 
x_26 = lean_box(0);
x_27 = lean_box(1);
x_28 = lean_box(1);
x_29 = lean_unbox(x_26);
x_30 = lean_unbox(x_27);
x_31 = lean_unbox(x_26);
x_32 = lean_unbox(x_28);
x_33 = l_Lean_Meta_mkLambdaFVars(x_9, x_17, x_29, x_30, x_31, x_32, x_22, x_23, x_24, x_25, x_16);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_array_to_list(x_21);
x_37 = l_Lean_Expr_const___override(x_19, x_36);
x_38 = l_Lean_mkAppN(x_37, x_20);
x_39 = l_Lean_Expr_app___override(x_38, x_34);
x_40 = l_Lean_mkAppN(x_39, x_18);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_40);
x_41 = l_Lean_Meta_isTypeCorrect(x_40, x_22, x_23, x_24, x_25, x_35);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed), 11, 4);
lean_closure_set(x_44, 0, x_4);
lean_closure_set(x_44, 1, x_26);
lean_closure_set(x_44, 2, x_27);
lean_closure_set(x_44, 3, x_28);
x_45 = lean_unbox(x_42);
lean_dec(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_44);
lean_dec(x_40);
x_46 = l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1;
x_47 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_46, x_22, x_23, x_24, x_25, x_43);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
lean_object* x_52; 
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_52 = lean_infer_type(x_40, x_22, x_23, x_24, x_25, x_43);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_unbox(x_26);
x_56 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(x_53, x_44, x_55, x_22, x_23, x_24, x_25, x_54);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_44);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_40);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_41);
if (x_61 == 0)
{
return x_41;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_41, 0);
x_63 = lean_ctor_get(x_41, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_41);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_33);
if (x_65 == 0)
{
return x_33;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_33, 0);
x_67 = lean_ctor_get(x_33, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_33);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 5);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 6);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 7);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_instInhabitedExpr;
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed), 15, 8);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_14);
lean_closure_set(x_16, 4, x_10);
lean_closure_set(x_16, 5, x_8);
lean_closure_set(x_16, 6, x_11);
lean_closure_set(x_16, 7, x_9);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_12, x_16, x_18, x_3, x_4, x_5, x_6, x_7);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_foldRevM_loop___at___Lean_Meta_MatcherApp_refineThrough_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___lam__0(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_refineThrough_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
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
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
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
lean_dec(x_2);
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Meta_MatcherApp_refineThrough___lam__0(x_1, x_12, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_MatcherApp_refineThrough___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_8);
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
lean_dec(x_27);
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
lean_dec(x_6);
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
lean_inc(x_9);
x_10 = l_Array_zip___redArg(x_1, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_10);
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
lean_dec(x_10);
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
lean_dec(x_10);
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
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
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
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
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
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2;
x_5 = l_Lean_throwError___redArg(x_1, x_2, x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_push(x_1, x_7);
x_9 = lean_nat_add(x_2, x_3);
lean_inc(x_5);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__4___boxed), 5, 4);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_inc(x_13);
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
lean_dec(x_13);
lean_dec(x_4);
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
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__3___boxed), 5, 4);
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
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_38; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
lean_inc(x_2);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed), 7, 6);
lean_closure_set(x_31, 0, x_12);
lean_closure_set(x_31, 1, x_11);
lean_closure_set(x_31, 2, x_24);
lean_closure_set(x_31, 3, x_10);
lean_closure_set(x_31, 4, x_1);
lean_closure_set(x_31, 5, x_2);
x_38 = lean_unbox(x_30);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = lean_unbox(x_30);
lean_dec(x_30);
x_32 = x_39;
goto block_37;
}
else
{
lean_dec(x_30);
x_32 = x_16;
goto block_37;
}
block_37:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_box(x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed), 7, 2);
lean_closure_set(x_34, 0, x_33);
lean_closure_set(x_34, 1, x_4);
x_35 = lean_apply_2(x_3, lean_box(0), x_34);
x_36 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_35, x_31);
return x_36;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_10);
x_40 = lean_array_fget(x_13, x_14);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_14, x_41);
lean_dec(x_14);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_13);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_15);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__3___boxed), 5, 4);
lean_closure_set(x_44, 0, x_11);
lean_closure_set(x_44, 1, x_12);
lean_closure_set(x_44, 2, x_43);
lean_closure_set(x_44, 3, x_1);
x_45 = lean_box(0);
x_46 = lean_apply_2(x_1, lean_box(0), x_45);
x_47 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_46, x_44);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_56; 
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
lean_dec(x_40);
lean_inc(x_2);
x_49 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed), 7, 6);
lean_closure_set(x_49, 0, x_12);
lean_closure_set(x_49, 1, x_11);
lean_closure_set(x_49, 2, x_41);
lean_closure_set(x_49, 3, x_43);
lean_closure_set(x_49, 4, x_1);
lean_closure_set(x_49, 5, x_2);
x_56 = lean_unbox(x_48);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = lean_unbox(x_48);
lean_dec(x_48);
x_50 = x_57;
goto block_55;
}
else
{
lean_dec(x_48);
x_50 = x_16;
goto block_55;
}
block_55:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_box(x_50);
x_52 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed), 7, 2);
lean_closure_set(x_52, 0, x_51);
lean_closure_set(x_52, 1, x_4);
x_53 = lean_apply_2(x_3, lean_box(0), x_52);
x_54 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_53, x_49);
return x_54;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_58 = lean_ctor_get(x_6, 0);
x_59 = lean_ctor_get(x_8, 0);
x_60 = lean_ctor_get(x_8, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_8);
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_58, 2);
lean_inc(x_63);
x_64 = lean_nat_dec_lt(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_60);
lean_ctor_set(x_6, 1, x_65);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_6);
x_67 = lean_apply_2(x_1, lean_box(0), x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_free_object(x_6);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 x_68 = x_58;
} else {
 lean_dec_ref(x_58);
 x_68 = lean_box(0);
}
x_69 = lean_array_fget(x_61, x_62);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_62, x_70);
lean_dec(x_62);
if (lean_is_scalar(x_68)) {
 x_72 = lean_alloc_ctor(0, 3, 0);
} else {
 x_72 = x_68;
}
lean_ctor_set(x_72, 0, x_61);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_63);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_73 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__3___boxed), 5, 4);
lean_closure_set(x_73, 0, x_59);
lean_closure_set(x_73, 1, x_60);
lean_closure_set(x_73, 2, x_72);
lean_closure_set(x_73, 3, x_1);
x_74 = lean_box(0);
x_75 = lean_apply_2(x_1, lean_box(0), x_74);
x_76 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_75, x_73);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_85; 
x_77 = lean_ctor_get(x_69, 0);
lean_inc(x_77);
lean_dec(x_69);
lean_inc(x_2);
x_78 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed), 7, 6);
lean_closure_set(x_78, 0, x_60);
lean_closure_set(x_78, 1, x_59);
lean_closure_set(x_78, 2, x_70);
lean_closure_set(x_78, 3, x_72);
lean_closure_set(x_78, 4, x_1);
lean_closure_set(x_78, 5, x_2);
x_85 = lean_unbox(x_77);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = lean_unbox(x_77);
lean_dec(x_77);
x_79 = x_86;
goto block_84;
}
else
{
lean_dec(x_77);
x_79 = x_64;
goto block_84;
}
block_84:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_box(x_79);
x_81 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed), 7, 2);
lean_closure_set(x_81, 0, x_80);
lean_closure_set(x_81, 1, x_4);
x_82 = lean_apply_2(x_3, lean_box(0), x_81);
x_83 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_82, x_78);
return x_83;
}
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_87 = lean_ctor_get(x_6, 1);
x_88 = lean_ctor_get(x_6, 0);
lean_inc(x_87);
lean_inc(x_88);
lean_dec(x_6);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_91 = x_87;
} else {
 lean_dec_ref(x_87);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_88, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_88, 2);
lean_inc(x_94);
x_95 = lean_nat_dec_lt(x_93, x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_91)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_91;
}
lean_ctor_set(x_96, 0, x_89);
lean_ctor_set(x_96, 1, x_90);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_88);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_apply_2(x_1, lean_box(0), x_98);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_91);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 x_100 = x_88;
} else {
 lean_dec_ref(x_88);
 x_100 = lean_box(0);
}
x_101 = lean_array_fget(x_92, x_93);
x_102 = lean_unsigned_to_nat(1u);
x_103 = lean_nat_add(x_93, x_102);
lean_dec(x_93);
if (lean_is_scalar(x_100)) {
 x_104 = lean_alloc_ctor(0, 3, 0);
} else {
 x_104 = x_100;
}
lean_ctor_set(x_104, 0, x_92);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_104, 2, x_94);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_105 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__3___boxed), 5, 4);
lean_closure_set(x_105, 0, x_89);
lean_closure_set(x_105, 1, x_90);
lean_closure_set(x_105, 2, x_104);
lean_closure_set(x_105, 3, x_1);
x_106 = lean_box(0);
x_107 = lean_apply_2(x_1, lean_box(0), x_106);
x_108 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_107, x_105);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_117; 
x_109 = lean_ctor_get(x_101, 0);
lean_inc(x_109);
lean_dec(x_101);
lean_inc(x_2);
x_110 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed), 7, 6);
lean_closure_set(x_110, 0, x_90);
lean_closure_set(x_110, 1, x_89);
lean_closure_set(x_110, 2, x_102);
lean_closure_set(x_110, 3, x_104);
lean_closure_set(x_110, 4, x_1);
lean_closure_set(x_110, 5, x_2);
x_117 = lean_unbox(x_109);
if (x_117 == 0)
{
uint8_t x_118; 
x_118 = lean_unbox(x_109);
lean_dec(x_109);
x_111 = x_118;
goto block_116;
}
else
{
lean_dec(x_109);
x_111 = x_95;
goto block_116;
}
block_116:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_box(x_111);
x_113 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed), 7, 2);
lean_closure_set(x_113, 0, x_112);
lean_closure_set(x_113, 1, x_4);
x_114 = lean_apply_2(x_3, lean_box(0), x_113);
x_115 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_114, x_110);
return x_115;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkArrow___redArg(x_1, x_2, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_Expr_isHEq(x_1);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_array_push(x_2, x_10);
lean_inc(x_5);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed), 6, 5);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed), 7, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed), 7, 6);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11) {
_start:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_array_push(x_6, x_15);
lean_inc(x_10);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed), 6, 5);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_inc(x_18);
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
lean_dec(x_18);
lean_dec(x_5);
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
lean_inc(x_28);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_13, 2);
lean_inc(x_30);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_19, x_31);
lean_inc(x_18);
lean_ctor_set(x_12, 1, x_32);
x_33 = lean_nat_dec_lt(x_29, x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_5);
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
lean_inc(x_28);
lean_ctor_set(x_13, 1, x_40);
if (x_3 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_array_fget(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_16);
lean_inc(x_17);
x_49 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12), 8, 7);
lean_closure_set(x_49, 0, x_17);
lean_closure_set(x_49, 1, x_16);
lean_closure_set(x_49, 2, x_12);
lean_closure_set(x_49, 3, x_13);
lean_closure_set(x_49, 4, x_1);
lean_closure_set(x_49, 5, x_2);
lean_closure_set(x_49, 6, x_4);
x_50 = lean_array_fget(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_5);
x_51 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14___boxed), 11, 10);
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
lean_dec(x_28);
lean_dec(x_5);
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
x_43 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed), 6, 5);
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
lean_inc(x_28);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_28);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_30);
if (x_3 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_array_fget(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_56);
lean_inc(x_12);
lean_inc(x_16);
lean_inc(x_17);
x_65 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12), 8, 7);
lean_closure_set(x_65, 0, x_17);
lean_closure_set(x_65, 1, x_16);
lean_closure_set(x_65, 2, x_12);
lean_closure_set(x_65, 3, x_56);
lean_closure_set(x_65, 4, x_1);
lean_closure_set(x_65, 5, x_2);
lean_closure_set(x_65, 6, x_4);
x_66 = lean_array_fget(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_5);
x_67 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14___boxed), 11, 10);
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
lean_dec(x_28);
lean_dec(x_5);
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
x_59 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed), 6, 5);
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
lean_inc(x_71);
x_72 = lean_ctor_get(x_13, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_13, 2);
lean_inc(x_73);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_add(x_19, x_74);
lean_inc(x_18);
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
lean_dec(x_71);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_5);
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
lean_inc(x_71);
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
lean_dec(x_71);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_array_fget(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_82);
lean_inc(x_76);
lean_inc(x_16);
lean_inc(x_17);
x_91 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12), 8, 7);
lean_closure_set(x_91, 0, x_17);
lean_closure_set(x_91, 1, x_16);
lean_closure_set(x_91, 2, x_76);
lean_closure_set(x_91, 3, x_82);
lean_closure_set(x_91, 4, x_1);
lean_closure_set(x_91, 5, x_2);
lean_closure_set(x_91, 6, x_4);
x_92 = lean_array_fget(x_71, x_72);
lean_dec(x_72);
lean_dec(x_71);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_5);
x_93 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14___boxed), 11, 10);
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
lean_dec(x_71);
lean_dec(x_5);
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
x_85 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed), 6, 5);
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
lean_inc(x_99);
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
lean_dec(x_99);
lean_dec(x_5);
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
lean_inc(x_107);
x_108 = lean_ctor_get(x_13, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_13, 2);
lean_inc(x_109);
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_nat_add(x_100, x_110);
lean_inc(x_99);
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
lean_dec(x_107);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_5);
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
lean_inc(x_107);
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
lean_dec(x_107);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_5);
lean_dec(x_4);
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_array_fget(x_99, x_100);
lean_dec(x_100);
lean_dec(x_99);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_119);
lean_inc(x_112);
lean_inc(x_97);
lean_inc(x_98);
x_128 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12), 8, 7);
lean_closure_set(x_128, 0, x_98);
lean_closure_set(x_128, 1, x_97);
lean_closure_set(x_128, 2, x_112);
lean_closure_set(x_128, 3, x_119);
lean_closure_set(x_128, 4, x_1);
lean_closure_set(x_128, 5, x_2);
lean_closure_set(x_128, 6, x_4);
x_129 = lean_array_fget(x_107, x_108);
lean_dec(x_108);
lean_dec(x_107);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_5);
x_130 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14___boxed), 11, 10);
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
lean_dec(x_107);
lean_dec(x_5);
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
x_122 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed), 6, 5);
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
lean_inc(x_140);
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
lean_dec(x_140);
lean_dec(x_5);
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
lean_inc(x_149);
x_150 = lean_ctor_get(x_136, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_136, 2);
lean_inc(x_151);
x_152 = lean_unsigned_to_nat(1u);
x_153 = lean_nat_add(x_141, x_152);
lean_inc(x_140);
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
lean_dec(x_149);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_5);
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
lean_inc(x_149);
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
lean_dec(x_149);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_5);
lean_dec(x_4);
goto block_169;
}
else
{
lean_object* x_170; 
x_170 = lean_array_fget(x_140, x_141);
lean_dec(x_141);
lean_dec(x_140);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_162);
lean_inc(x_154);
lean_inc(x_137);
lean_inc(x_138);
x_171 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12), 8, 7);
lean_closure_set(x_171, 0, x_138);
lean_closure_set(x_171, 1, x_137);
lean_closure_set(x_171, 2, x_154);
lean_closure_set(x_171, 3, x_162);
lean_closure_set(x_171, 4, x_1);
lean_closure_set(x_171, 5, x_2);
lean_closure_set(x_171, 6, x_4);
x_172 = lean_array_fget(x_149, x_150);
lean_dec(x_150);
lean_dec(x_149);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_5);
x_173 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14___boxed), 11, 10);
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
lean_dec(x_149);
lean_dec(x_5);
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
x_165 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed), 6, 5);
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
lean_inc(x_184);
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
lean_dec(x_184);
lean_dec(x_5);
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
lean_inc(x_194);
x_195 = lean_ctor_get(x_179, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_179, 2);
lean_inc(x_196);
x_197 = lean_unsigned_to_nat(1u);
x_198 = lean_nat_add(x_185, x_197);
lean_inc(x_184);
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
lean_dec(x_194);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_5);
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
lean_inc(x_194);
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
lean_dec(x_194);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_5);
lean_dec(x_4);
goto block_215;
}
else
{
lean_object* x_216; 
x_216 = lean_array_fget(x_184, x_185);
lean_dec(x_185);
lean_dec(x_184);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_208);
lean_inc(x_199);
lean_inc(x_181);
lean_inc(x_182);
x_217 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12), 8, 7);
lean_closure_set(x_217, 0, x_182);
lean_closure_set(x_217, 1, x_181);
lean_closure_set(x_217, 2, x_199);
lean_closure_set(x_217, 3, x_208);
lean_closure_set(x_217, 4, x_1);
lean_closure_set(x_217, 5, x_2);
lean_closure_set(x_217, 6, x_4);
x_218 = lean_array_fget(x_194, x_195);
lean_dec(x_195);
lean_dec(x_194);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_5);
x_219 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14___boxed), 11, 10);
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
lean_dec(x_194);
lean_dec(x_5);
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
x_211 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed), 6, 5);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__15), 4, 3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
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
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16), 6, 5);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_9);
lean_closure_set(x_10, 3, x_2);
lean_closure_set(x_10, 4, x_3);
x_11 = lean_box(0);
x_12 = lean_box(1);
x_13 = lean_box(1);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 11, 6);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_9);
lean_closure_set(x_14, 2, x_11);
lean_closure_set(x_14, 3, x_12);
lean_closure_set(x_14, 4, x_11);
lean_closure_set(x_14, 5, x_13);
x_15 = lean_apply_2(x_2, lean_box(0), x_14);
x_16 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_15, x_10);
return x_16;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__18___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Meta_MatcherApp_transform___redArg___lam__18___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_2(x_1, x_2, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_inc(x_11);
lean_inc(x_3);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__17), 5, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_11);
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__18), 8, 7);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_5);
lean_closure_set(x_14, 2, x_11);
lean_closure_set(x_14, 3, x_6);
lean_closure_set(x_14, 4, x_7);
lean_closure_set(x_14, 5, x_3);
lean_closure_set(x_14, 6, x_13);
lean_inc(x_3);
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed), 6, 5);
lean_closure_set(x_15, 0, x_8);
lean_closure_set(x_15, 1, x_11);
lean_closure_set(x_15, 2, x_12);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_14);
x_16 = lean_array_get_size(x_11);
lean_dec(x_11);
x_17 = lean_array_get_size(x_9);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__20), 2, 1);
lean_closure_set(x_19, 0, x_15);
x_20 = l_Lean_Meta_MatcherApp_addArg___lam__1___closed__4;
x_21 = l_Nat_reprFast(x_17);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_MessageData_ofFormat(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Meta_MatcherApp_addArg___lam__1___closed__6;
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
lean_dec(x_10);
lean_dec(x_6);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__20), 2, 1);
lean_closure_set(x_29, 0, x_15);
x_30 = lean_box(0);
x_31 = lean_apply_2(x_1, lean_box(0), x_30);
x_32 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_31, x_29);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_add(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Array_append___redArg(x_1, x_2);
x_8 = lean_box(1);
x_9 = lean_box(x_3);
x_10 = lean_box(x_4);
x_11 = lean_box(x_3);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 11, 6);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_9);
lean_closure_set(x_12, 3, x_10);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_8);
x_13 = lean_apply_2(x_5, lean_box(0), x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_3(x_1, x_2, x_3, x_6);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_apply_2(x_3, lean_box(0), x_9);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_5);
x_12 = l_Lean_Meta_MatcherApp_withUserNames___redArg(x_6, x_7, x_2, x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_box(x_2);
x_15 = lean_box(x_3);
lean_inc(x_4);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed), 6, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_12);
lean_closure_set(x_16, 2, x_14);
lean_closure_set(x_16, 3, x_15);
lean_closure_set(x_16, 4, x_4);
lean_inc(x_7);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__24), 6, 5);
lean_closure_set(x_17, 0, x_5);
lean_closure_set(x_17, 1, x_6);
lean_closure_set(x_17, 2, x_13);
lean_closure_set(x_17, 3, x_7);
lean_closure_set(x_17, 4, x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_8);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__25), 8, 7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_box(x_1);
x_15 = lean_box(x_2);
lean_inc(x_9);
lean_inc(x_8);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed), 13, 11);
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
x_18 = l_Lean_Meta_forallBoundedTelescope___redArg(x_8, x_9, x_13, x_17, x_16, x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_push(x_1, x_7);
lean_inc(x_5);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__28___boxed), 6, 5);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_4);
lean_closure_set(x_9, 4, x_5);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_5, lean_box(0), x_10);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
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
lean_inc(x_26);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_16, 2);
lean_inc(x_28);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_13);
x_31 = lean_apply_2(x_1, lean_box(0), x_30);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_33 = lean_ctor_get(x_16, 2);
lean_dec(x_33);
x_34 = lean_ctor_get(x_16, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_16, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_21, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_21, 2);
lean_inc(x_38);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_27, x_39);
lean_inc(x_26);
lean_ctor_set(x_16, 1, x_40);
x_41 = lean_nat_dec_lt(x_37, x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_13);
x_43 = lean_apply_2(x_1, lean_box(0), x_42);
return x_43;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_21);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_45 = lean_ctor_get(x_21, 2);
lean_dec(x_45);
x_46 = lean_ctor_get(x_21, 1);
lean_dec(x_46);
x_47 = lean_ctor_get(x_21, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_18, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_18, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_18, 2);
lean_inc(x_50);
x_51 = lean_nat_add(x_37, x_39);
lean_inc(x_36);
lean_ctor_set(x_21, 1, x_51);
x_52 = lean_nat_dec_lt(x_49, x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_13);
x_54 = lean_apply_2(x_1, lean_box(0), x_53);
return x_54;
}
else
{
uint8_t x_55; 
lean_free_object(x_15);
lean_free_object(x_14);
lean_free_object(x_13);
x_55 = !lean_is_exclusive(x_18);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_56 = lean_ctor_get(x_18, 2);
lean_dec(x_56);
x_57 = lean_ctor_get(x_18, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_18, 0);
lean_dec(x_58);
x_59 = lean_array_fget(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_60 = lean_array_fget(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
x_61 = lean_array_fget(x_48, x_49);
x_62 = lean_box(x_2);
x_63 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_64 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed), 13, 11);
lean_closure_set(x_64, 0, x_62);
lean_closure_set(x_64, 1, x_63);
lean_closure_set(x_64, 2, x_4);
lean_closure_set(x_64, 3, x_5);
lean_closure_set(x_64, 4, x_11);
lean_closure_set(x_64, 5, x_6);
lean_closure_set(x_64, 6, x_61);
lean_closure_set(x_64, 7, x_7);
lean_closure_set(x_64, 8, x_8);
lean_closure_set(x_64, 9, x_9);
lean_closure_set(x_64, 10, x_10);
x_65 = lean_nat_add(x_49, x_39);
lean_dec(x_49);
lean_ctor_set(x_18, 1, x_65);
lean_inc(x_6);
x_66 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__29), 7, 6);
lean_closure_set(x_66, 0, x_24);
lean_closure_set(x_66, 1, x_16);
lean_closure_set(x_66, 2, x_21);
lean_closure_set(x_66, 3, x_18);
lean_closure_set(x_66, 4, x_1);
lean_closure_set(x_66, 5, x_6);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_60);
x_68 = l_Lean_Meta_forallBoundedTelescope___redArg(x_7, x_8, x_59, x_67, x_64, x_2);
x_69 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_68, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_18);
x_70 = lean_array_fget(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_71 = lean_array_fget(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
x_72 = lean_array_fget(x_48, x_49);
x_73 = lean_box(x_2);
x_74 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_75 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed), 13, 11);
lean_closure_set(x_75, 0, x_73);
lean_closure_set(x_75, 1, x_74);
lean_closure_set(x_75, 2, x_4);
lean_closure_set(x_75, 3, x_5);
lean_closure_set(x_75, 4, x_11);
lean_closure_set(x_75, 5, x_6);
lean_closure_set(x_75, 6, x_72);
lean_closure_set(x_75, 7, x_7);
lean_closure_set(x_75, 8, x_8);
lean_closure_set(x_75, 9, x_9);
lean_closure_set(x_75, 10, x_10);
x_76 = lean_nat_add(x_49, x_39);
lean_dec(x_49);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_48);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_50);
lean_inc(x_6);
x_78 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__29), 7, 6);
lean_closure_set(x_78, 0, x_24);
lean_closure_set(x_78, 1, x_16);
lean_closure_set(x_78, 2, x_21);
lean_closure_set(x_78, 3, x_77);
lean_closure_set(x_78, 4, x_1);
lean_closure_set(x_78, 5, x_6);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_71);
x_80 = l_Lean_Meta_forallBoundedTelescope___redArg(x_7, x_8, x_70, x_79, x_75, x_2);
x_81 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_80, x_78);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec(x_21);
x_82 = lean_ctor_get(x_18, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_18, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_18, 2);
lean_inc(x_84);
x_85 = lean_nat_add(x_37, x_39);
lean_inc(x_36);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_36);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_38);
x_87 = lean_nat_dec_lt(x_83, x_84);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_14, 0, x_86);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_13);
x_89 = lean_apply_2(x_1, lean_box(0), x_88);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_free_object(x_15);
lean_free_object(x_14);
lean_free_object(x_13);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_90 = x_18;
} else {
 lean_dec_ref(x_18);
 x_90 = lean_box(0);
}
x_91 = lean_array_fget(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_92 = lean_array_fget(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
x_93 = lean_array_fget(x_82, x_83);
x_94 = lean_box(x_2);
x_95 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_96 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed), 13, 11);
lean_closure_set(x_96, 0, x_94);
lean_closure_set(x_96, 1, x_95);
lean_closure_set(x_96, 2, x_4);
lean_closure_set(x_96, 3, x_5);
lean_closure_set(x_96, 4, x_11);
lean_closure_set(x_96, 5, x_6);
lean_closure_set(x_96, 6, x_93);
lean_closure_set(x_96, 7, x_7);
lean_closure_set(x_96, 8, x_8);
lean_closure_set(x_96, 9, x_9);
lean_closure_set(x_96, 10, x_10);
x_97 = lean_nat_add(x_83, x_39);
lean_dec(x_83);
if (lean_is_scalar(x_90)) {
 x_98 = lean_alloc_ctor(0, 3, 0);
} else {
 x_98 = x_90;
}
lean_ctor_set(x_98, 0, x_82);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_98, 2, x_84);
lean_inc(x_6);
x_99 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__29), 7, 6);
lean_closure_set(x_99, 0, x_24);
lean_closure_set(x_99, 1, x_16);
lean_closure_set(x_99, 2, x_86);
lean_closure_set(x_99, 3, x_98);
lean_closure_set(x_99, 4, x_1);
lean_closure_set(x_99, 5, x_6);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_92);
x_101 = l_Lean_Meta_forallBoundedTelescope___redArg(x_7, x_8, x_91, x_100, x_96, x_2);
x_102 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_101, x_99);
return x_102;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec(x_16);
x_103 = lean_ctor_get(x_21, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_21, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_21, 2);
lean_inc(x_105);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_add(x_27, x_106);
lean_inc(x_26);
x_108 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_108, 0, x_26);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_108, 2, x_28);
x_109 = lean_nat_dec_lt(x_104, x_105);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_15, 0, x_108);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_13);
x_111 = lean_apply_2(x_1, lean_box(0), x_110);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_112 = x_21;
} else {
 lean_dec_ref(x_21);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_18, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_18, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_18, 2);
lean_inc(x_115);
x_116 = lean_nat_add(x_104, x_106);
lean_inc(x_103);
if (lean_is_scalar(x_112)) {
 x_117 = lean_alloc_ctor(0, 3, 0);
} else {
 x_117 = x_112;
}
lean_ctor_set(x_117, 0, x_103);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_117, 2, x_105);
x_118 = lean_nat_dec_lt(x_114, x_115);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_15, 0, x_108);
lean_ctor_set(x_14, 0, x_117);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_13);
x_120 = lean_apply_2(x_1, lean_box(0), x_119);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_free_object(x_15);
lean_free_object(x_14);
lean_free_object(x_13);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_121 = x_18;
} else {
 lean_dec_ref(x_18);
 x_121 = lean_box(0);
}
x_122 = lean_array_fget(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_123 = lean_array_fget(x_103, x_104);
lean_dec(x_104);
lean_dec(x_103);
x_124 = lean_array_fget(x_113, x_114);
x_125 = lean_box(x_2);
x_126 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_127 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed), 13, 11);
lean_closure_set(x_127, 0, x_125);
lean_closure_set(x_127, 1, x_126);
lean_closure_set(x_127, 2, x_4);
lean_closure_set(x_127, 3, x_5);
lean_closure_set(x_127, 4, x_11);
lean_closure_set(x_127, 5, x_6);
lean_closure_set(x_127, 6, x_124);
lean_closure_set(x_127, 7, x_7);
lean_closure_set(x_127, 8, x_8);
lean_closure_set(x_127, 9, x_9);
lean_closure_set(x_127, 10, x_10);
x_128 = lean_nat_add(x_114, x_106);
lean_dec(x_114);
if (lean_is_scalar(x_121)) {
 x_129 = lean_alloc_ctor(0, 3, 0);
} else {
 x_129 = x_121;
}
lean_ctor_set(x_129, 0, x_113);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_115);
lean_inc(x_6);
x_130 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__29), 7, 6);
lean_closure_set(x_130, 0, x_24);
lean_closure_set(x_130, 1, x_108);
lean_closure_set(x_130, 2, x_117);
lean_closure_set(x_130, 3, x_129);
lean_closure_set(x_130, 4, x_1);
lean_closure_set(x_130, 5, x_6);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_123);
x_132 = l_Lean_Meta_forallBoundedTelescope___redArg(x_7, x_8, x_122, x_131, x_127, x_2);
x_133 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_132, x_130);
return x_133;
}
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_134 = lean_ctor_get(x_15, 1);
lean_inc(x_134);
lean_dec(x_15);
x_135 = lean_ctor_get(x_16, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_16, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_16, 2);
lean_inc(x_137);
x_138 = lean_nat_dec_lt(x_136, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_16);
lean_ctor_set(x_139, 1, x_134);
lean_ctor_set(x_14, 1, x_139);
x_140 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_140, 0, x_13);
x_141 = lean_apply_2(x_1, lean_box(0), x_140);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 x_142 = x_16;
} else {
 lean_dec_ref(x_16);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_21, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_21, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_21, 2);
lean_inc(x_145);
x_146 = lean_unsigned_to_nat(1u);
x_147 = lean_nat_add(x_136, x_146);
lean_inc(x_135);
if (lean_is_scalar(x_142)) {
 x_148 = lean_alloc_ctor(0, 3, 0);
} else {
 x_148 = x_142;
}
lean_ctor_set(x_148, 0, x_135);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_148, 2, x_137);
x_149 = lean_nat_dec_lt(x_144, x_145);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_134);
lean_ctor_set(x_14, 1, x_150);
x_151 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_151, 0, x_13);
x_152 = lean_apply_2(x_1, lean_box(0), x_151);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_153 = x_21;
} else {
 lean_dec_ref(x_21);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_18, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_18, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_18, 2);
lean_inc(x_156);
x_157 = lean_nat_add(x_144, x_146);
lean_inc(x_143);
if (lean_is_scalar(x_153)) {
 x_158 = lean_alloc_ctor(0, 3, 0);
} else {
 x_158 = x_153;
}
lean_ctor_set(x_158, 0, x_143);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set(x_158, 2, x_145);
x_159 = lean_nat_dec_lt(x_155, x_156);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_148);
lean_ctor_set(x_160, 1, x_134);
lean_ctor_set(x_14, 1, x_160);
lean_ctor_set(x_14, 0, x_158);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_13);
x_162 = lean_apply_2(x_1, lean_box(0), x_161);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_free_object(x_14);
lean_free_object(x_13);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_163 = x_18;
} else {
 lean_dec_ref(x_18);
 x_163 = lean_box(0);
}
x_164 = lean_array_fget(x_135, x_136);
lean_dec(x_136);
lean_dec(x_135);
x_165 = lean_array_fget(x_143, x_144);
lean_dec(x_144);
lean_dec(x_143);
x_166 = lean_array_fget(x_154, x_155);
x_167 = lean_box(x_2);
x_168 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_169 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed), 13, 11);
lean_closure_set(x_169, 0, x_167);
lean_closure_set(x_169, 1, x_168);
lean_closure_set(x_169, 2, x_4);
lean_closure_set(x_169, 3, x_5);
lean_closure_set(x_169, 4, x_11);
lean_closure_set(x_169, 5, x_6);
lean_closure_set(x_169, 6, x_166);
lean_closure_set(x_169, 7, x_7);
lean_closure_set(x_169, 8, x_8);
lean_closure_set(x_169, 9, x_9);
lean_closure_set(x_169, 10, x_10);
x_170 = lean_nat_add(x_155, x_146);
lean_dec(x_155);
if (lean_is_scalar(x_163)) {
 x_171 = lean_alloc_ctor(0, 3, 0);
} else {
 x_171 = x_163;
}
lean_ctor_set(x_171, 0, x_154);
lean_ctor_set(x_171, 1, x_170);
lean_ctor_set(x_171, 2, x_156);
lean_inc(x_6);
x_172 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__29), 7, 6);
lean_closure_set(x_172, 0, x_134);
lean_closure_set(x_172, 1, x_148);
lean_closure_set(x_172, 2, x_158);
lean_closure_set(x_172, 3, x_171);
lean_closure_set(x_172, 4, x_1);
lean_closure_set(x_172, 5, x_6);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_165);
x_174 = l_Lean_Meta_forallBoundedTelescope___redArg(x_7, x_8, x_164, x_173, x_169, x_2);
x_175 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_174, x_172);
return x_175;
}
}
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_176 = lean_ctor_get(x_14, 0);
lean_inc(x_176);
lean_dec(x_14);
x_177 = lean_ctor_get(x_15, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_178 = x_15;
} else {
 lean_dec_ref(x_15);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_16, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_16, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_16, 2);
lean_inc(x_181);
x_182 = lean_nat_dec_lt(x_180, x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_178)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_178;
}
lean_ctor_set(x_183, 0, x_16);
lean_ctor_set(x_183, 1, x_177);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_176);
lean_ctor_set(x_184, 1, x_183);
lean_ctor_set(x_13, 1, x_184);
x_185 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_185, 0, x_13);
x_186 = lean_apply_2(x_1, lean_box(0), x_185);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 x_187 = x_16;
} else {
 lean_dec_ref(x_16);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_176, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_176, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_176, 2);
lean_inc(x_190);
x_191 = lean_unsigned_to_nat(1u);
x_192 = lean_nat_add(x_180, x_191);
lean_inc(x_179);
if (lean_is_scalar(x_187)) {
 x_193 = lean_alloc_ctor(0, 3, 0);
} else {
 x_193 = x_187;
}
lean_ctor_set(x_193, 0, x_179);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set(x_193, 2, x_181);
x_194 = lean_nat_dec_lt(x_189, x_190);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_178)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_178;
}
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_177);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_176);
lean_ctor_set(x_196, 1, x_195);
lean_ctor_set(x_13, 1, x_196);
x_197 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_197, 0, x_13);
x_198 = lean_apply_2(x_1, lean_box(0), x_197);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 lean_ctor_release(x_176, 2);
 x_199 = x_176;
} else {
 lean_dec_ref(x_176);
 x_199 = lean_box(0);
}
x_200 = lean_ctor_get(x_18, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_18, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_18, 2);
lean_inc(x_202);
x_203 = lean_nat_add(x_189, x_191);
lean_inc(x_188);
if (lean_is_scalar(x_199)) {
 x_204 = lean_alloc_ctor(0, 3, 0);
} else {
 x_204 = x_199;
}
lean_ctor_set(x_204, 0, x_188);
lean_ctor_set(x_204, 1, x_203);
lean_ctor_set(x_204, 2, x_190);
x_205 = lean_nat_dec_lt(x_201, x_202);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_178)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_178;
}
lean_ctor_set(x_206, 0, x_193);
lean_ctor_set(x_206, 1, x_177);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_206);
lean_ctor_set(x_13, 1, x_207);
x_208 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_208, 0, x_13);
x_209 = lean_apply_2(x_1, lean_box(0), x_208);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_178);
lean_free_object(x_13);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_210 = x_18;
} else {
 lean_dec_ref(x_18);
 x_210 = lean_box(0);
}
x_211 = lean_array_fget(x_179, x_180);
lean_dec(x_180);
lean_dec(x_179);
x_212 = lean_array_fget(x_188, x_189);
lean_dec(x_189);
lean_dec(x_188);
x_213 = lean_array_fget(x_200, x_201);
x_214 = lean_box(x_2);
x_215 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_216 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed), 13, 11);
lean_closure_set(x_216, 0, x_214);
lean_closure_set(x_216, 1, x_215);
lean_closure_set(x_216, 2, x_4);
lean_closure_set(x_216, 3, x_5);
lean_closure_set(x_216, 4, x_11);
lean_closure_set(x_216, 5, x_6);
lean_closure_set(x_216, 6, x_213);
lean_closure_set(x_216, 7, x_7);
lean_closure_set(x_216, 8, x_8);
lean_closure_set(x_216, 9, x_9);
lean_closure_set(x_216, 10, x_10);
x_217 = lean_nat_add(x_201, x_191);
lean_dec(x_201);
if (lean_is_scalar(x_210)) {
 x_218 = lean_alloc_ctor(0, 3, 0);
} else {
 x_218 = x_210;
}
lean_ctor_set(x_218, 0, x_200);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set(x_218, 2, x_202);
lean_inc(x_6);
x_219 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__29), 7, 6);
lean_closure_set(x_219, 0, x_177);
lean_closure_set(x_219, 1, x_193);
lean_closure_set(x_219, 2, x_204);
lean_closure_set(x_219, 3, x_218);
lean_closure_set(x_219, 4, x_1);
lean_closure_set(x_219, 5, x_6);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_212);
x_221 = l_Lean_Meta_forallBoundedTelescope___redArg(x_7, x_8, x_211, x_220, x_216, x_2);
x_222 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_221, x_219);
return x_222;
}
}
}
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_223 = lean_ctor_get(x_13, 0);
lean_inc(x_223);
lean_dec(x_13);
x_224 = lean_ctor_get(x_14, 0);
lean_inc(x_224);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_225 = x_14;
} else {
 lean_dec_ref(x_14);
 x_225 = lean_box(0);
}
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
lean_inc(x_228);
x_229 = lean_ctor_get(x_16, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_16, 2);
lean_inc(x_230);
x_231 = lean_nat_dec_lt(x_229, x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_227)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_227;
}
lean_ctor_set(x_232, 0, x_16);
lean_ctor_set(x_232, 1, x_226);
if (lean_is_scalar(x_225)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_225;
}
lean_ctor_set(x_233, 0, x_224);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_223);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_235, 0, x_234);
x_236 = lean_apply_2(x_1, lean_box(0), x_235);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 x_237 = x_16;
} else {
 lean_dec_ref(x_16);
 x_237 = lean_box(0);
}
x_238 = lean_ctor_get(x_224, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_224, 1);
lean_inc(x_239);
x_240 = lean_ctor_get(x_224, 2);
lean_inc(x_240);
x_241 = lean_unsigned_to_nat(1u);
x_242 = lean_nat_add(x_229, x_241);
lean_inc(x_228);
if (lean_is_scalar(x_237)) {
 x_243 = lean_alloc_ctor(0, 3, 0);
} else {
 x_243 = x_237;
}
lean_ctor_set(x_243, 0, x_228);
lean_ctor_set(x_243, 1, x_242);
lean_ctor_set(x_243, 2, x_230);
x_244 = lean_nat_dec_lt(x_239, x_240);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_227)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_227;
}
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_226);
if (lean_is_scalar(x_225)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_225;
}
lean_ctor_set(x_246, 0, x_224);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_223);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_248, 0, x_247);
x_249 = lean_apply_2(x_1, lean_box(0), x_248);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 lean_ctor_release(x_224, 2);
 x_250 = x_224;
} else {
 lean_dec_ref(x_224);
 x_250 = lean_box(0);
}
x_251 = lean_ctor_get(x_223, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_223, 1);
lean_inc(x_252);
x_253 = lean_ctor_get(x_223, 2);
lean_inc(x_253);
x_254 = lean_nat_add(x_239, x_241);
lean_inc(x_238);
if (lean_is_scalar(x_250)) {
 x_255 = lean_alloc_ctor(0, 3, 0);
} else {
 x_255 = x_250;
}
lean_ctor_set(x_255, 0, x_238);
lean_ctor_set(x_255, 1, x_254);
lean_ctor_set(x_255, 2, x_240);
x_256 = lean_nat_dec_lt(x_252, x_253);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_227)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_227;
}
lean_ctor_set(x_257, 0, x_243);
lean_ctor_set(x_257, 1, x_226);
if (lean_is_scalar(x_225)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_225;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_223);
lean_ctor_set(x_259, 1, x_258);
x_260 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_260, 0, x_259);
x_261 = lean_apply_2(x_1, lean_box(0), x_260);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_227);
lean_dec(x_225);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 lean_ctor_release(x_223, 2);
 x_262 = x_223;
} else {
 lean_dec_ref(x_223);
 x_262 = lean_box(0);
}
x_263 = lean_array_fget(x_228, x_229);
lean_dec(x_229);
lean_dec(x_228);
x_264 = lean_array_fget(x_238, x_239);
lean_dec(x_239);
lean_dec(x_238);
x_265 = lean_array_fget(x_251, x_252);
x_266 = lean_box(x_2);
x_267 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_268 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed), 13, 11);
lean_closure_set(x_268, 0, x_266);
lean_closure_set(x_268, 1, x_267);
lean_closure_set(x_268, 2, x_4);
lean_closure_set(x_268, 3, x_5);
lean_closure_set(x_268, 4, x_11);
lean_closure_set(x_268, 5, x_6);
lean_closure_set(x_268, 6, x_265);
lean_closure_set(x_268, 7, x_7);
lean_closure_set(x_268, 8, x_8);
lean_closure_set(x_268, 9, x_9);
lean_closure_set(x_268, 10, x_10);
x_269 = lean_nat_add(x_252, x_241);
lean_dec(x_252);
if (lean_is_scalar(x_262)) {
 x_270 = lean_alloc_ctor(0, 3, 0);
} else {
 x_270 = x_262;
}
lean_ctor_set(x_270, 0, x_251);
lean_ctor_set(x_270, 1, x_269);
lean_ctor_set(x_270, 2, x_253);
lean_inc(x_6);
x_271 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__29), 7, 6);
lean_closure_set(x_271, 0, x_226);
lean_closure_set(x_271, 1, x_243);
lean_closure_set(x_271, 2, x_255);
lean_closure_set(x_271, 3, x_270);
lean_closure_set(x_271, 4, x_1);
lean_closure_set(x_271, 5, x_6);
x_272 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_272, 0, x_264);
x_273 = l_Lean_Meta_forallBoundedTelescope___redArg(x_7, x_8, x_263, x_272, x_268, x_2);
x_274 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_273, x_271);
return x_274;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__1;
x_2 = l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__5;
x_2 = l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__4;
x_3 = l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__3;
x_4 = l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__2;
x_5 = l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__6;
x_2 = l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = l_Array_append___redArg(x_1, x_13);
x_15 = l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__9;
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 13, 12);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Array_toSubarray___redArg(x_1, x_2, x_3);
x_12 = lean_array_get_size(x_4);
lean_inc(x_2);
x_13 = l_Array_toSubarray___redArg(x_4, x_2, x_12);
x_14 = lean_array_get_size(x_10);
lean_inc(x_2);
x_15 = l_Array_toSubarray___redArg(x_10, x_2, x_14);
x_16 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Std_Range_forIn_x27_loop___redArg(x_6, x_17, x_7, x_20, x_2);
x_22 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_21, x_9);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_inc(x_13);
lean_inc(x_1);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 15, 14);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_3);
lean_closure_set(x_23, 4, x_4);
lean_closure_set(x_23, 5, x_5);
lean_closure_set(x_23, 6, x_6);
lean_closure_set(x_23, 7, x_7);
lean_closure_set(x_23, 8, x_8);
lean_closure_set(x_23, 9, x_9);
lean_closure_set(x_23, 10, x_10);
lean_closure_set(x_23, 11, x_11);
lean_closure_set(x_23, 12, x_12);
lean_closure_set(x_23, 13, x_13);
x_24 = lean_array_get_size(x_14);
lean_inc(x_13);
lean_inc(x_24);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33), 10, 9);
lean_closure_set(x_25, 0, x_14);
lean_closure_set(x_25, 1, x_15);
lean_closure_set(x_25, 2, x_24);
lean_closure_set(x_25, 3, x_1);
lean_closure_set(x_25, 4, x_16);
lean_closure_set(x_25, 5, x_17);
lean_closure_set(x_25, 6, x_18);
lean_closure_set(x_25, 7, x_13);
lean_closure_set(x_25, 8, x_23);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN), 7, 2);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_19);
x_27 = lean_apply_2(x_20, lean_box(0), x_26);
x_28 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_27, x_25);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to transform matcher, type error when constructing new motive:", 69, 69);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10) {
_start:
{
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__1;
x_12 = l_Lean_indentExpr(x_1);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__3;
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_apply_2(x_8, lean_box(0), x_18);
x_20 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_19, x_9);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = l_Array_append___redArg(x_1, x_2);
x_10 = l_Array_append___redArg(x_9, x_3);
x_11 = l_Array_append___redArg(x_10, x_4);
x_12 = lean_box(1);
x_13 = lean_box(x_5);
x_14 = lean_box(x_6);
x_15 = lean_box(x_5);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 11, 6);
lean_closure_set(x_16, 0, x_11);
lean_closure_set(x_16, 1, x_8);
lean_closure_set(x_16, 2, x_13);
lean_closure_set(x_16, 3, x_14);
lean_closure_set(x_16, 4, x_15);
lean_closure_set(x_16, 5, x_12);
x_17 = lean_apply_2(x_7, lean_box(0), x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_3(x_1, x_2, x_3, x_6);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(x_5);
x_19 = lean_box(x_6);
lean_inc(x_7);
lean_inc(x_4);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37___boxed), 8, 7);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_3);
lean_closure_set(x_20, 2, x_4);
lean_closure_set(x_20, 3, x_14);
lean_closure_set(x_20, 4, x_18);
lean_closure_set(x_20, 5, x_19);
lean_closure_set(x_20, 6, x_7);
lean_inc(x_10);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__39), 6, 5);
lean_closure_set(x_21, 0, x_8);
lean_closure_set(x_21, 1, x_9);
lean_closure_set(x_21, 2, x_15);
lean_closure_set(x_21, 3, x_10);
lean_closure_set(x_21, 4, x_20);
x_22 = l_Array_append___redArg(x_11, x_4);
lean_dec(x_4);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(x_23, 0, x_12);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_apply_2(x_7, lean_box(0), x_23);
x_25 = lean_apply_3(x_17, lean_box(0), x_24, x_13);
x_26 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_25, x_21);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_box(x_4);
x_19 = lean_box(x_5);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 15, 13);
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
x_22 = l_Lean_Meta_forallBoundedTelescope___redArg(x_14, x_15, x_17, x_21, x_20, x_4);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_box(x_3);
x_19 = lean_box(x_4);
lean_inc(x_14);
lean_inc(x_13);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed), 17, 15);
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
x_22 = l_Lean_Meta_forallBoundedTelescope___redArg(x_13, x_14, x_17, x_21, x_20, x_3);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_Meta_forallBoundedTelescope___redArg(x_3, x_4, x_7, x_10, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_box(x_2);
x_19 = lean_box(x_3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_16);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__42___boxed), 17, 15);
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
lean_inc(x_16);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed), 7, 6);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_push(x_1, x_9);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__45___boxed), 8, 7);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_6);
lean_closure_set(x_11, 6, x_7);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_7, lean_box(0), x_12);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_13, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_20, 1);
x_36 = lean_ctor_get(x_20, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_21, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_21, 2);
lean_inc(x_39);
x_40 = lean_nat_dec_lt(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_16);
x_42 = lean_apply_2(x_1, lean_box(0), x_41);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_21);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_44 = lean_ctor_get(x_21, 2);
lean_dec(x_44);
x_45 = lean_ctor_get(x_21, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_21, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_32, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_32, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_32, 2);
lean_inc(x_49);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_38, x_50);
lean_inc(x_37);
lean_ctor_set(x_21, 1, x_51);
x_52 = lean_nat_dec_lt(x_48, x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_16);
x_54 = lean_apply_2(x_1, lean_box(0), x_53);
return x_54;
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_32);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_56 = lean_ctor_get(x_32, 2);
lean_dec(x_56);
x_57 = lean_ctor_get(x_32, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_32, 0);
lean_dec(x_58);
x_59 = lean_ctor_get(x_29, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_29, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_29, 2);
lean_inc(x_61);
x_62 = lean_nat_add(x_48, x_50);
lean_inc(x_47);
lean_ctor_set(x_32, 1, x_62);
x_63 = lean_nat_dec_lt(x_60, x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_16);
x_65 = lean_apply_2(x_1, lean_box(0), x_64);
return x_65;
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_29);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_67 = lean_ctor_get(x_29, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_29, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_29, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_26, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_26, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_26, 2);
lean_inc(x_72);
x_73 = lean_nat_add(x_60, x_50);
lean_inc(x_59);
lean_ctor_set(x_29, 1, x_73);
x_74 = lean_nat_dec_lt(x_71, x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_16);
x_76 = lean_apply_2(x_1, lean_box(0), x_75);
return x_76;
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_26);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_78 = lean_ctor_get(x_26, 2);
lean_dec(x_78);
x_79 = lean_ctor_get(x_26, 1);
lean_dec(x_79);
x_80 = lean_ctor_get(x_26, 0);
lean_dec(x_80);
x_81 = lean_ctor_get(x_23, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_23, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_23, 2);
lean_inc(x_83);
x_84 = lean_nat_add(x_71, x_50);
lean_inc(x_70);
lean_ctor_set(x_26, 1, x_84);
x_85 = lean_nat_dec_lt(x_82, x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_16);
x_87 = lean_apply_2(x_1, lean_box(0), x_86);
return x_87;
}
else
{
uint8_t x_88; 
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_18);
lean_free_object(x_17);
lean_free_object(x_16);
x_88 = !lean_is_exclusive(x_23);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_89 = lean_ctor_get(x_23, 2);
lean_dec(x_89);
x_90 = lean_ctor_get(x_23, 1);
lean_dec(x_90);
x_91 = lean_ctor_get(x_23, 0);
lean_dec(x_91);
x_92 = lean_array_fget(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
x_93 = lean_array_fget(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
x_94 = lean_array_fget(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
x_95 = lean_array_fget(x_70, x_71);
lean_dec(x_71);
lean_dec(x_70);
x_96 = lean_array_fget(x_81, x_82);
x_97 = lean_box(x_3);
x_98 = lean_box(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_99 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 17, 15);
lean_closure_set(x_99, 0, x_2);
lean_closure_set(x_99, 1, x_97);
lean_closure_set(x_99, 2, x_98);
lean_closure_set(x_99, 3, x_5);
lean_closure_set(x_99, 4, x_6);
lean_closure_set(x_99, 5, x_14);
lean_closure_set(x_99, 6, x_7);
lean_closure_set(x_99, 7, x_96);
lean_closure_set(x_99, 8, x_8);
lean_closure_set(x_99, 9, x_9);
lean_closure_set(x_99, 10, x_10);
lean_closure_set(x_99, 11, x_11);
lean_closure_set(x_99, 12, x_12);
lean_closure_set(x_99, 13, x_94);
lean_closure_set(x_99, 14, x_92);
x_100 = lean_nat_add(x_82, x_50);
lean_dec(x_82);
lean_ctor_set(x_23, 1, x_100);
lean_inc(x_7);
x_101 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46), 9, 8);
lean_closure_set(x_101, 0, x_35);
lean_closure_set(x_101, 1, x_21);
lean_closure_set(x_101, 2, x_32);
lean_closure_set(x_101, 3, x_29);
lean_closure_set(x_101, 4, x_26);
lean_closure_set(x_101, 5, x_23);
lean_closure_set(x_101, 6, x_1);
lean_closure_set(x_101, 7, x_7);
x_102 = lean_nat_sub(x_95, x_12);
lean_dec(x_12);
lean_dec(x_95);
x_103 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_11, x_10, x_93, x_102, x_13, x_99);
x_104 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_103, x_101);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_23);
x_105 = lean_array_fget(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
x_106 = lean_array_fget(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
x_107 = lean_array_fget(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
x_108 = lean_array_fget(x_70, x_71);
lean_dec(x_71);
lean_dec(x_70);
x_109 = lean_array_fget(x_81, x_82);
x_110 = lean_box(x_3);
x_111 = lean_box(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_112 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 17, 15);
lean_closure_set(x_112, 0, x_2);
lean_closure_set(x_112, 1, x_110);
lean_closure_set(x_112, 2, x_111);
lean_closure_set(x_112, 3, x_5);
lean_closure_set(x_112, 4, x_6);
lean_closure_set(x_112, 5, x_14);
lean_closure_set(x_112, 6, x_7);
lean_closure_set(x_112, 7, x_109);
lean_closure_set(x_112, 8, x_8);
lean_closure_set(x_112, 9, x_9);
lean_closure_set(x_112, 10, x_10);
lean_closure_set(x_112, 11, x_11);
lean_closure_set(x_112, 12, x_12);
lean_closure_set(x_112, 13, x_107);
lean_closure_set(x_112, 14, x_105);
x_113 = lean_nat_add(x_82, x_50);
lean_dec(x_82);
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_81);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_114, 2, x_83);
lean_inc(x_7);
x_115 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46), 9, 8);
lean_closure_set(x_115, 0, x_35);
lean_closure_set(x_115, 1, x_21);
lean_closure_set(x_115, 2, x_32);
lean_closure_set(x_115, 3, x_29);
lean_closure_set(x_115, 4, x_26);
lean_closure_set(x_115, 5, x_114);
lean_closure_set(x_115, 6, x_1);
lean_closure_set(x_115, 7, x_7);
x_116 = lean_nat_sub(x_108, x_12);
lean_dec(x_12);
lean_dec(x_108);
x_117 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_11, x_10, x_106, x_116, x_13, x_112);
x_118 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_117, x_115);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
lean_dec(x_26);
x_119 = lean_ctor_get(x_23, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_23, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_23, 2);
lean_inc(x_121);
x_122 = lean_nat_add(x_71, x_50);
lean_inc(x_70);
x_123 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_123, 0, x_70);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_123, 2, x_72);
x_124 = lean_nat_dec_lt(x_120, x_121);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_ctor_set(x_17, 0, x_123);
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_16);
x_126 = lean_apply_2(x_1, lean_box(0), x_125);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_18);
lean_free_object(x_17);
lean_free_object(x_16);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_127 = x_23;
} else {
 lean_dec_ref(x_23);
 x_127 = lean_box(0);
}
x_128 = lean_array_fget(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
x_129 = lean_array_fget(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
x_130 = lean_array_fget(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
x_131 = lean_array_fget(x_70, x_71);
lean_dec(x_71);
lean_dec(x_70);
x_132 = lean_array_fget(x_119, x_120);
x_133 = lean_box(x_3);
x_134 = lean_box(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_135 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 17, 15);
lean_closure_set(x_135, 0, x_2);
lean_closure_set(x_135, 1, x_133);
lean_closure_set(x_135, 2, x_134);
lean_closure_set(x_135, 3, x_5);
lean_closure_set(x_135, 4, x_6);
lean_closure_set(x_135, 5, x_14);
lean_closure_set(x_135, 6, x_7);
lean_closure_set(x_135, 7, x_132);
lean_closure_set(x_135, 8, x_8);
lean_closure_set(x_135, 9, x_9);
lean_closure_set(x_135, 10, x_10);
lean_closure_set(x_135, 11, x_11);
lean_closure_set(x_135, 12, x_12);
lean_closure_set(x_135, 13, x_130);
lean_closure_set(x_135, 14, x_128);
x_136 = lean_nat_add(x_120, x_50);
lean_dec(x_120);
if (lean_is_scalar(x_127)) {
 x_137 = lean_alloc_ctor(0, 3, 0);
} else {
 x_137 = x_127;
}
lean_ctor_set(x_137, 0, x_119);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set(x_137, 2, x_121);
lean_inc(x_7);
x_138 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46), 9, 8);
lean_closure_set(x_138, 0, x_35);
lean_closure_set(x_138, 1, x_21);
lean_closure_set(x_138, 2, x_32);
lean_closure_set(x_138, 3, x_29);
lean_closure_set(x_138, 4, x_123);
lean_closure_set(x_138, 5, x_137);
lean_closure_set(x_138, 6, x_1);
lean_closure_set(x_138, 7, x_7);
x_139 = lean_nat_sub(x_131, x_12);
lean_dec(x_12);
lean_dec(x_131);
x_140 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_11, x_10, x_129, x_139, x_13, x_135);
x_141 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_140, x_138);
return x_141;
}
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
lean_dec(x_29);
x_142 = lean_ctor_get(x_26, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_26, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_26, 2);
lean_inc(x_144);
x_145 = lean_nat_add(x_60, x_50);
lean_inc(x_59);
x_146 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_146, 0, x_59);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_146, 2, x_61);
x_147 = lean_nat_dec_lt(x_143, x_144);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_ctor_set(x_18, 0, x_146);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_16);
x_149 = lean_apply_2(x_1, lean_box(0), x_148);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_150 = x_26;
} else {
 lean_dec_ref(x_26);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_23, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_23, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_23, 2);
lean_inc(x_153);
x_154 = lean_nat_add(x_143, x_50);
lean_inc(x_142);
if (lean_is_scalar(x_150)) {
 x_155 = lean_alloc_ctor(0, 3, 0);
} else {
 x_155 = x_150;
}
lean_ctor_set(x_155, 0, x_142);
lean_ctor_set(x_155, 1, x_154);
lean_ctor_set(x_155, 2, x_144);
x_156 = lean_nat_dec_lt(x_152, x_153);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_ctor_set(x_18, 0, x_146);
lean_ctor_set(x_17, 0, x_155);
x_157 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_157, 0, x_16);
x_158 = lean_apply_2(x_1, lean_box(0), x_157);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_18);
lean_free_object(x_17);
lean_free_object(x_16);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_159 = x_23;
} else {
 lean_dec_ref(x_23);
 x_159 = lean_box(0);
}
x_160 = lean_array_fget(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
x_161 = lean_array_fget(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
x_162 = lean_array_fget(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
x_163 = lean_array_fget(x_142, x_143);
lean_dec(x_143);
lean_dec(x_142);
x_164 = lean_array_fget(x_151, x_152);
x_165 = lean_box(x_3);
x_166 = lean_box(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_167 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 17, 15);
lean_closure_set(x_167, 0, x_2);
lean_closure_set(x_167, 1, x_165);
lean_closure_set(x_167, 2, x_166);
lean_closure_set(x_167, 3, x_5);
lean_closure_set(x_167, 4, x_6);
lean_closure_set(x_167, 5, x_14);
lean_closure_set(x_167, 6, x_7);
lean_closure_set(x_167, 7, x_164);
lean_closure_set(x_167, 8, x_8);
lean_closure_set(x_167, 9, x_9);
lean_closure_set(x_167, 10, x_10);
lean_closure_set(x_167, 11, x_11);
lean_closure_set(x_167, 12, x_12);
lean_closure_set(x_167, 13, x_162);
lean_closure_set(x_167, 14, x_160);
x_168 = lean_nat_add(x_152, x_50);
lean_dec(x_152);
if (lean_is_scalar(x_159)) {
 x_169 = lean_alloc_ctor(0, 3, 0);
} else {
 x_169 = x_159;
}
lean_ctor_set(x_169, 0, x_151);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set(x_169, 2, x_153);
lean_inc(x_7);
x_170 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46), 9, 8);
lean_closure_set(x_170, 0, x_35);
lean_closure_set(x_170, 1, x_21);
lean_closure_set(x_170, 2, x_32);
lean_closure_set(x_170, 3, x_146);
lean_closure_set(x_170, 4, x_155);
lean_closure_set(x_170, 5, x_169);
lean_closure_set(x_170, 6, x_1);
lean_closure_set(x_170, 7, x_7);
x_171 = lean_nat_sub(x_163, x_12);
lean_dec(x_12);
lean_dec(x_163);
x_172 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_11, x_10, x_161, x_171, x_13, x_167);
x_173 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_172, x_170);
return x_173;
}
}
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
lean_dec(x_32);
x_174 = lean_ctor_get(x_29, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_29, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_29, 2);
lean_inc(x_176);
x_177 = lean_nat_add(x_48, x_50);
lean_inc(x_47);
x_178 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_178, 0, x_47);
lean_ctor_set(x_178, 1, x_177);
lean_ctor_set(x_178, 2, x_49);
x_179 = lean_nat_dec_lt(x_175, x_176);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_ctor_set(x_19, 0, x_178);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_16);
x_181 = lean_apply_2(x_1, lean_box(0), x_180);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 x_182 = x_29;
} else {
 lean_dec_ref(x_29);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_26, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_26, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_26, 2);
lean_inc(x_185);
x_186 = lean_nat_add(x_175, x_50);
lean_inc(x_174);
if (lean_is_scalar(x_182)) {
 x_187 = lean_alloc_ctor(0, 3, 0);
} else {
 x_187 = x_182;
}
lean_ctor_set(x_187, 0, x_174);
lean_ctor_set(x_187, 1, x_186);
lean_ctor_set(x_187, 2, x_176);
x_188 = lean_nat_dec_lt(x_184, x_185);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_ctor_set(x_19, 0, x_178);
lean_ctor_set(x_18, 0, x_187);
x_189 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_189, 0, x_16);
x_190 = lean_apply_2(x_1, lean_box(0), x_189);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_191 = x_26;
} else {
 lean_dec_ref(x_26);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_23, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_23, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_23, 2);
lean_inc(x_194);
x_195 = lean_nat_add(x_184, x_50);
lean_inc(x_183);
if (lean_is_scalar(x_191)) {
 x_196 = lean_alloc_ctor(0, 3, 0);
} else {
 x_196 = x_191;
}
lean_ctor_set(x_196, 0, x_183);
lean_ctor_set(x_196, 1, x_195);
lean_ctor_set(x_196, 2, x_185);
x_197 = lean_nat_dec_lt(x_193, x_194);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_ctor_set(x_19, 0, x_178);
lean_ctor_set(x_18, 0, x_187);
lean_ctor_set(x_17, 0, x_196);
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_16);
x_199 = lean_apply_2(x_1, lean_box(0), x_198);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_18);
lean_free_object(x_17);
lean_free_object(x_16);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_200 = x_23;
} else {
 lean_dec_ref(x_23);
 x_200 = lean_box(0);
}
x_201 = lean_array_fget(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
x_202 = lean_array_fget(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
x_203 = lean_array_fget(x_174, x_175);
lean_dec(x_175);
lean_dec(x_174);
x_204 = lean_array_fget(x_183, x_184);
lean_dec(x_184);
lean_dec(x_183);
x_205 = lean_array_fget(x_192, x_193);
x_206 = lean_box(x_3);
x_207 = lean_box(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_208 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 17, 15);
lean_closure_set(x_208, 0, x_2);
lean_closure_set(x_208, 1, x_206);
lean_closure_set(x_208, 2, x_207);
lean_closure_set(x_208, 3, x_5);
lean_closure_set(x_208, 4, x_6);
lean_closure_set(x_208, 5, x_14);
lean_closure_set(x_208, 6, x_7);
lean_closure_set(x_208, 7, x_205);
lean_closure_set(x_208, 8, x_8);
lean_closure_set(x_208, 9, x_9);
lean_closure_set(x_208, 10, x_10);
lean_closure_set(x_208, 11, x_11);
lean_closure_set(x_208, 12, x_12);
lean_closure_set(x_208, 13, x_203);
lean_closure_set(x_208, 14, x_201);
x_209 = lean_nat_add(x_193, x_50);
lean_dec(x_193);
if (lean_is_scalar(x_200)) {
 x_210 = lean_alloc_ctor(0, 3, 0);
} else {
 x_210 = x_200;
}
lean_ctor_set(x_210, 0, x_192);
lean_ctor_set(x_210, 1, x_209);
lean_ctor_set(x_210, 2, x_194);
lean_inc(x_7);
x_211 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46), 9, 8);
lean_closure_set(x_211, 0, x_35);
lean_closure_set(x_211, 1, x_21);
lean_closure_set(x_211, 2, x_178);
lean_closure_set(x_211, 3, x_187);
lean_closure_set(x_211, 4, x_196);
lean_closure_set(x_211, 5, x_210);
lean_closure_set(x_211, 6, x_1);
lean_closure_set(x_211, 7, x_7);
x_212 = lean_nat_sub(x_204, x_12);
lean_dec(x_12);
lean_dec(x_204);
x_213 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_11, x_10, x_202, x_212, x_13, x_208);
x_214 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_213, x_211);
return x_214;
}
}
}
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
lean_dec(x_21);
x_215 = lean_ctor_get(x_32, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_32, 1);
lean_inc(x_216);
x_217 = lean_ctor_get(x_32, 2);
lean_inc(x_217);
x_218 = lean_unsigned_to_nat(1u);
x_219 = lean_nat_add(x_38, x_218);
lean_inc(x_37);
x_220 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_220, 0, x_37);
lean_ctor_set(x_220, 1, x_219);
lean_ctor_set(x_220, 2, x_39);
x_221 = lean_nat_dec_lt(x_216, x_217);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_ctor_set(x_20, 0, x_220);
x_222 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_222, 0, x_16);
x_223 = lean_apply_2(x_1, lean_box(0), x_222);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 x_224 = x_32;
} else {
 lean_dec_ref(x_32);
 x_224 = lean_box(0);
}
x_225 = lean_ctor_get(x_29, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_29, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_29, 2);
lean_inc(x_227);
x_228 = lean_nat_add(x_216, x_218);
lean_inc(x_215);
if (lean_is_scalar(x_224)) {
 x_229 = lean_alloc_ctor(0, 3, 0);
} else {
 x_229 = x_224;
}
lean_ctor_set(x_229, 0, x_215);
lean_ctor_set(x_229, 1, x_228);
lean_ctor_set(x_229, 2, x_217);
x_230 = lean_nat_dec_lt(x_226, x_227);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_ctor_set(x_20, 0, x_220);
lean_ctor_set(x_19, 0, x_229);
x_231 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_231, 0, x_16);
x_232 = lean_apply_2(x_1, lean_box(0), x_231);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 x_233 = x_29;
} else {
 lean_dec_ref(x_29);
 x_233 = lean_box(0);
}
x_234 = lean_ctor_get(x_26, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_26, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_26, 2);
lean_inc(x_236);
x_237 = lean_nat_add(x_226, x_218);
lean_inc(x_225);
if (lean_is_scalar(x_233)) {
 x_238 = lean_alloc_ctor(0, 3, 0);
} else {
 x_238 = x_233;
}
lean_ctor_set(x_238, 0, x_225);
lean_ctor_set(x_238, 1, x_237);
lean_ctor_set(x_238, 2, x_227);
x_239 = lean_nat_dec_lt(x_235, x_236);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_ctor_set(x_20, 0, x_220);
lean_ctor_set(x_19, 0, x_229);
lean_ctor_set(x_18, 0, x_238);
x_240 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_240, 0, x_16);
x_241 = lean_apply_2(x_1, lean_box(0), x_240);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_242 = x_26;
} else {
 lean_dec_ref(x_26);
 x_242 = lean_box(0);
}
x_243 = lean_ctor_get(x_23, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_23, 1);
lean_inc(x_244);
x_245 = lean_ctor_get(x_23, 2);
lean_inc(x_245);
x_246 = lean_nat_add(x_235, x_218);
lean_inc(x_234);
if (lean_is_scalar(x_242)) {
 x_247 = lean_alloc_ctor(0, 3, 0);
} else {
 x_247 = x_242;
}
lean_ctor_set(x_247, 0, x_234);
lean_ctor_set(x_247, 1, x_246);
lean_ctor_set(x_247, 2, x_236);
x_248 = lean_nat_dec_lt(x_244, x_245);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_ctor_set(x_20, 0, x_220);
lean_ctor_set(x_19, 0, x_229);
lean_ctor_set(x_18, 0, x_238);
lean_ctor_set(x_17, 0, x_247);
x_249 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_249, 0, x_16);
x_250 = lean_apply_2(x_1, lean_box(0), x_249);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_18);
lean_free_object(x_17);
lean_free_object(x_16);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_251 = x_23;
} else {
 lean_dec_ref(x_23);
 x_251 = lean_box(0);
}
x_252 = lean_array_fget(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
x_253 = lean_array_fget(x_215, x_216);
lean_dec(x_216);
lean_dec(x_215);
x_254 = lean_array_fget(x_225, x_226);
lean_dec(x_226);
lean_dec(x_225);
x_255 = lean_array_fget(x_234, x_235);
lean_dec(x_235);
lean_dec(x_234);
x_256 = lean_array_fget(x_243, x_244);
x_257 = lean_box(x_3);
x_258 = lean_box(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_259 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 17, 15);
lean_closure_set(x_259, 0, x_2);
lean_closure_set(x_259, 1, x_257);
lean_closure_set(x_259, 2, x_258);
lean_closure_set(x_259, 3, x_5);
lean_closure_set(x_259, 4, x_6);
lean_closure_set(x_259, 5, x_14);
lean_closure_set(x_259, 6, x_7);
lean_closure_set(x_259, 7, x_256);
lean_closure_set(x_259, 8, x_8);
lean_closure_set(x_259, 9, x_9);
lean_closure_set(x_259, 10, x_10);
lean_closure_set(x_259, 11, x_11);
lean_closure_set(x_259, 12, x_12);
lean_closure_set(x_259, 13, x_254);
lean_closure_set(x_259, 14, x_252);
x_260 = lean_nat_add(x_244, x_218);
lean_dec(x_244);
if (lean_is_scalar(x_251)) {
 x_261 = lean_alloc_ctor(0, 3, 0);
} else {
 x_261 = x_251;
}
lean_ctor_set(x_261, 0, x_243);
lean_ctor_set(x_261, 1, x_260);
lean_ctor_set(x_261, 2, x_245);
lean_inc(x_7);
x_262 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46), 9, 8);
lean_closure_set(x_262, 0, x_35);
lean_closure_set(x_262, 1, x_220);
lean_closure_set(x_262, 2, x_229);
lean_closure_set(x_262, 3, x_238);
lean_closure_set(x_262, 4, x_247);
lean_closure_set(x_262, 5, x_261);
lean_closure_set(x_262, 6, x_1);
lean_closure_set(x_262, 7, x_7);
x_263 = lean_nat_sub(x_255, x_12);
lean_dec(x_12);
lean_dec(x_255);
x_264 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_11, x_10, x_253, x_263, x_13, x_259);
x_265 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_264, x_262);
return x_265;
}
}
}
}
}
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_266 = lean_ctor_get(x_20, 1);
lean_inc(x_266);
lean_dec(x_20);
x_267 = lean_ctor_get(x_21, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_21, 1);
lean_inc(x_268);
x_269 = lean_ctor_get(x_21, 2);
lean_inc(x_269);
x_270 = lean_nat_dec_lt(x_268, x_269);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_21);
lean_ctor_set(x_271, 1, x_266);
lean_ctor_set(x_19, 1, x_271);
x_272 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_272, 0, x_16);
x_273 = lean_apply_2(x_1, lean_box(0), x_272);
return x_273;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_274 = x_21;
} else {
 lean_dec_ref(x_21);
 x_274 = lean_box(0);
}
x_275 = lean_ctor_get(x_32, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_32, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_32, 2);
lean_inc(x_277);
x_278 = lean_unsigned_to_nat(1u);
x_279 = lean_nat_add(x_268, x_278);
lean_inc(x_267);
if (lean_is_scalar(x_274)) {
 x_280 = lean_alloc_ctor(0, 3, 0);
} else {
 x_280 = x_274;
}
lean_ctor_set(x_280, 0, x_267);
lean_ctor_set(x_280, 1, x_279);
lean_ctor_set(x_280, 2, x_269);
x_281 = lean_nat_dec_lt(x_276, x_277);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_266);
lean_ctor_set(x_19, 1, x_282);
x_283 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_283, 0, x_16);
x_284 = lean_apply_2(x_1, lean_box(0), x_283);
return x_284;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 x_285 = x_32;
} else {
 lean_dec_ref(x_32);
 x_285 = lean_box(0);
}
x_286 = lean_ctor_get(x_29, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_29, 1);
lean_inc(x_287);
x_288 = lean_ctor_get(x_29, 2);
lean_inc(x_288);
x_289 = lean_nat_add(x_276, x_278);
lean_inc(x_275);
if (lean_is_scalar(x_285)) {
 x_290 = lean_alloc_ctor(0, 3, 0);
} else {
 x_290 = x_285;
}
lean_ctor_set(x_290, 0, x_275);
lean_ctor_set(x_290, 1, x_289);
lean_ctor_set(x_290, 2, x_277);
x_291 = lean_nat_dec_lt(x_287, x_288);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_280);
lean_ctor_set(x_292, 1, x_266);
lean_ctor_set(x_19, 1, x_292);
lean_ctor_set(x_19, 0, x_290);
x_293 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_293, 0, x_16);
x_294 = lean_apply_2(x_1, lean_box(0), x_293);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 x_295 = x_29;
} else {
 lean_dec_ref(x_29);
 x_295 = lean_box(0);
}
x_296 = lean_ctor_get(x_26, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_26, 1);
lean_inc(x_297);
x_298 = lean_ctor_get(x_26, 2);
lean_inc(x_298);
x_299 = lean_nat_add(x_287, x_278);
lean_inc(x_286);
if (lean_is_scalar(x_295)) {
 x_300 = lean_alloc_ctor(0, 3, 0);
} else {
 x_300 = x_295;
}
lean_ctor_set(x_300, 0, x_286);
lean_ctor_set(x_300, 1, x_299);
lean_ctor_set(x_300, 2, x_288);
x_301 = lean_nat_dec_lt(x_297, x_298);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_298);
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_280);
lean_ctor_set(x_302, 1, x_266);
lean_ctor_set(x_19, 1, x_302);
lean_ctor_set(x_19, 0, x_290);
lean_ctor_set(x_18, 0, x_300);
x_303 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_303, 0, x_16);
x_304 = lean_apply_2(x_1, lean_box(0), x_303);
return x_304;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; 
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_305 = x_26;
} else {
 lean_dec_ref(x_26);
 x_305 = lean_box(0);
}
x_306 = lean_ctor_get(x_23, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_23, 1);
lean_inc(x_307);
x_308 = lean_ctor_get(x_23, 2);
lean_inc(x_308);
x_309 = lean_nat_add(x_297, x_278);
lean_inc(x_296);
if (lean_is_scalar(x_305)) {
 x_310 = lean_alloc_ctor(0, 3, 0);
} else {
 x_310 = x_305;
}
lean_ctor_set(x_310, 0, x_296);
lean_ctor_set(x_310, 1, x_309);
lean_ctor_set(x_310, 2, x_298);
x_311 = lean_nat_dec_lt(x_307, x_308);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_308);
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_280);
lean_ctor_set(x_312, 1, x_266);
lean_ctor_set(x_19, 1, x_312);
lean_ctor_set(x_19, 0, x_290);
lean_ctor_set(x_18, 0, x_300);
lean_ctor_set(x_17, 0, x_310);
x_313 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_313, 0, x_16);
x_314 = lean_apply_2(x_1, lean_box(0), x_313);
return x_314;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_free_object(x_19);
lean_free_object(x_18);
lean_free_object(x_17);
lean_free_object(x_16);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_315 = x_23;
} else {
 lean_dec_ref(x_23);
 x_315 = lean_box(0);
}
x_316 = lean_array_fget(x_267, x_268);
lean_dec(x_268);
lean_dec(x_267);
x_317 = lean_array_fget(x_275, x_276);
lean_dec(x_276);
lean_dec(x_275);
x_318 = lean_array_fget(x_286, x_287);
lean_dec(x_287);
lean_dec(x_286);
x_319 = lean_array_fget(x_296, x_297);
lean_dec(x_297);
lean_dec(x_296);
x_320 = lean_array_fget(x_306, x_307);
x_321 = lean_box(x_3);
x_322 = lean_box(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_323 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 17, 15);
lean_closure_set(x_323, 0, x_2);
lean_closure_set(x_323, 1, x_321);
lean_closure_set(x_323, 2, x_322);
lean_closure_set(x_323, 3, x_5);
lean_closure_set(x_323, 4, x_6);
lean_closure_set(x_323, 5, x_14);
lean_closure_set(x_323, 6, x_7);
lean_closure_set(x_323, 7, x_320);
lean_closure_set(x_323, 8, x_8);
lean_closure_set(x_323, 9, x_9);
lean_closure_set(x_323, 10, x_10);
lean_closure_set(x_323, 11, x_11);
lean_closure_set(x_323, 12, x_12);
lean_closure_set(x_323, 13, x_318);
lean_closure_set(x_323, 14, x_316);
x_324 = lean_nat_add(x_307, x_278);
lean_dec(x_307);
if (lean_is_scalar(x_315)) {
 x_325 = lean_alloc_ctor(0, 3, 0);
} else {
 x_325 = x_315;
}
lean_ctor_set(x_325, 0, x_306);
lean_ctor_set(x_325, 1, x_324);
lean_ctor_set(x_325, 2, x_308);
lean_inc(x_7);
x_326 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46), 9, 8);
lean_closure_set(x_326, 0, x_266);
lean_closure_set(x_326, 1, x_280);
lean_closure_set(x_326, 2, x_290);
lean_closure_set(x_326, 3, x_300);
lean_closure_set(x_326, 4, x_310);
lean_closure_set(x_326, 5, x_325);
lean_closure_set(x_326, 6, x_1);
lean_closure_set(x_326, 7, x_7);
x_327 = lean_nat_sub(x_319, x_12);
lean_dec(x_12);
lean_dec(x_319);
x_328 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_11, x_10, x_317, x_327, x_13, x_323);
x_329 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_328, x_326);
return x_329;
}
}
}
}
}
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; 
x_330 = lean_ctor_get(x_19, 0);
lean_inc(x_330);
lean_dec(x_19);
x_331 = lean_ctor_get(x_20, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_332 = x_20;
} else {
 lean_dec_ref(x_20);
 x_332 = lean_box(0);
}
x_333 = lean_ctor_get(x_21, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_21, 1);
lean_inc(x_334);
x_335 = lean_ctor_get(x_21, 2);
lean_inc(x_335);
x_336 = lean_nat_dec_lt(x_334, x_335);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_332)) {
 x_337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_337 = x_332;
}
lean_ctor_set(x_337, 0, x_21);
lean_ctor_set(x_337, 1, x_331);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_330);
lean_ctor_set(x_338, 1, x_337);
lean_ctor_set(x_18, 1, x_338);
x_339 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_339, 0, x_16);
x_340 = lean_apply_2(x_1, lean_box(0), x_339);
return x_340;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_341 = x_21;
} else {
 lean_dec_ref(x_21);
 x_341 = lean_box(0);
}
x_342 = lean_ctor_get(x_330, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_330, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_330, 2);
lean_inc(x_344);
x_345 = lean_unsigned_to_nat(1u);
x_346 = lean_nat_add(x_334, x_345);
lean_inc(x_333);
if (lean_is_scalar(x_341)) {
 x_347 = lean_alloc_ctor(0, 3, 0);
} else {
 x_347 = x_341;
}
lean_ctor_set(x_347, 0, x_333);
lean_ctor_set(x_347, 1, x_346);
lean_ctor_set(x_347, 2, x_335);
x_348 = lean_nat_dec_lt(x_343, x_344);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_332)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_332;
}
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_331);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_330);
lean_ctor_set(x_350, 1, x_349);
lean_ctor_set(x_18, 1, x_350);
x_351 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_351, 0, x_16);
x_352 = lean_apply_2(x_1, lean_box(0), x_351);
return x_352;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; 
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 x_353 = x_330;
} else {
 lean_dec_ref(x_330);
 x_353 = lean_box(0);
}
x_354 = lean_ctor_get(x_29, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_29, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_29, 2);
lean_inc(x_356);
x_357 = lean_nat_add(x_343, x_345);
lean_inc(x_342);
if (lean_is_scalar(x_353)) {
 x_358 = lean_alloc_ctor(0, 3, 0);
} else {
 x_358 = x_353;
}
lean_ctor_set(x_358, 0, x_342);
lean_ctor_set(x_358, 1, x_357);
lean_ctor_set(x_358, 2, x_344);
x_359 = lean_nat_dec_lt(x_355, x_356);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_332)) {
 x_360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_360 = x_332;
}
lean_ctor_set(x_360, 0, x_347);
lean_ctor_set(x_360, 1, x_331);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_360);
lean_ctor_set(x_18, 1, x_361);
x_362 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_362, 0, x_16);
x_363 = lean_apply_2(x_1, lean_box(0), x_362);
return x_363;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; 
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 x_364 = x_29;
} else {
 lean_dec_ref(x_29);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_26, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_26, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_26, 2);
lean_inc(x_367);
x_368 = lean_nat_add(x_355, x_345);
lean_inc(x_354);
if (lean_is_scalar(x_364)) {
 x_369 = lean_alloc_ctor(0, 3, 0);
} else {
 x_369 = x_364;
}
lean_ctor_set(x_369, 0, x_354);
lean_ctor_set(x_369, 1, x_368);
lean_ctor_set(x_369, 2, x_356);
x_370 = lean_nat_dec_lt(x_366, x_367);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_367);
lean_dec(x_366);
lean_dec(x_365);
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_332)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_332;
}
lean_ctor_set(x_371, 0, x_347);
lean_ctor_set(x_371, 1, x_331);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_358);
lean_ctor_set(x_372, 1, x_371);
lean_ctor_set(x_18, 1, x_372);
lean_ctor_set(x_18, 0, x_369);
x_373 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_373, 0, x_16);
x_374 = lean_apply_2(x_1, lean_box(0), x_373);
return x_374;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; 
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_375 = x_26;
} else {
 lean_dec_ref(x_26);
 x_375 = lean_box(0);
}
x_376 = lean_ctor_get(x_23, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_23, 1);
lean_inc(x_377);
x_378 = lean_ctor_get(x_23, 2);
lean_inc(x_378);
x_379 = lean_nat_add(x_366, x_345);
lean_inc(x_365);
if (lean_is_scalar(x_375)) {
 x_380 = lean_alloc_ctor(0, 3, 0);
} else {
 x_380 = x_375;
}
lean_ctor_set(x_380, 0, x_365);
lean_ctor_set(x_380, 1, x_379);
lean_ctor_set(x_380, 2, x_367);
x_381 = lean_nat_dec_lt(x_377, x_378);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_378);
lean_dec(x_377);
lean_dec(x_376);
lean_dec(x_366);
lean_dec(x_365);
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_332)) {
 x_382 = lean_alloc_ctor(0, 2, 0);
} else {
 x_382 = x_332;
}
lean_ctor_set(x_382, 0, x_347);
lean_ctor_set(x_382, 1, x_331);
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_358);
lean_ctor_set(x_383, 1, x_382);
lean_ctor_set(x_18, 1, x_383);
lean_ctor_set(x_18, 0, x_369);
lean_ctor_set(x_17, 0, x_380);
x_384 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_384, 0, x_16);
x_385 = lean_apply_2(x_1, lean_box(0), x_384);
return x_385;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_332);
lean_free_object(x_18);
lean_free_object(x_17);
lean_free_object(x_16);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_386 = x_23;
} else {
 lean_dec_ref(x_23);
 x_386 = lean_box(0);
}
x_387 = lean_array_fget(x_333, x_334);
lean_dec(x_334);
lean_dec(x_333);
x_388 = lean_array_fget(x_342, x_343);
lean_dec(x_343);
lean_dec(x_342);
x_389 = lean_array_fget(x_354, x_355);
lean_dec(x_355);
lean_dec(x_354);
x_390 = lean_array_fget(x_365, x_366);
lean_dec(x_366);
lean_dec(x_365);
x_391 = lean_array_fget(x_376, x_377);
x_392 = lean_box(x_3);
x_393 = lean_box(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_394 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 17, 15);
lean_closure_set(x_394, 0, x_2);
lean_closure_set(x_394, 1, x_392);
lean_closure_set(x_394, 2, x_393);
lean_closure_set(x_394, 3, x_5);
lean_closure_set(x_394, 4, x_6);
lean_closure_set(x_394, 5, x_14);
lean_closure_set(x_394, 6, x_7);
lean_closure_set(x_394, 7, x_391);
lean_closure_set(x_394, 8, x_8);
lean_closure_set(x_394, 9, x_9);
lean_closure_set(x_394, 10, x_10);
lean_closure_set(x_394, 11, x_11);
lean_closure_set(x_394, 12, x_12);
lean_closure_set(x_394, 13, x_389);
lean_closure_set(x_394, 14, x_387);
x_395 = lean_nat_add(x_377, x_345);
lean_dec(x_377);
if (lean_is_scalar(x_386)) {
 x_396 = lean_alloc_ctor(0, 3, 0);
} else {
 x_396 = x_386;
}
lean_ctor_set(x_396, 0, x_376);
lean_ctor_set(x_396, 1, x_395);
lean_ctor_set(x_396, 2, x_378);
lean_inc(x_7);
x_397 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46), 9, 8);
lean_closure_set(x_397, 0, x_331);
lean_closure_set(x_397, 1, x_347);
lean_closure_set(x_397, 2, x_358);
lean_closure_set(x_397, 3, x_369);
lean_closure_set(x_397, 4, x_380);
lean_closure_set(x_397, 5, x_396);
lean_closure_set(x_397, 6, x_1);
lean_closure_set(x_397, 7, x_7);
x_398 = lean_nat_sub(x_390, x_12);
lean_dec(x_12);
lean_dec(x_390);
x_399 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_11, x_10, x_388, x_398, x_13, x_394);
x_400 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_399, x_397);
return x_400;
}
}
}
}
}
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; 
x_401 = lean_ctor_get(x_18, 0);
lean_inc(x_401);
lean_dec(x_18);
x_402 = lean_ctor_get(x_19, 0);
lean_inc(x_402);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_403 = x_19;
} else {
 lean_dec_ref(x_19);
 x_403 = lean_box(0);
}
x_404 = lean_ctor_get(x_20, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_405 = x_20;
} else {
 lean_dec_ref(x_20);
 x_405 = lean_box(0);
}
x_406 = lean_ctor_get(x_21, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_21, 1);
lean_inc(x_407);
x_408 = lean_ctor_get(x_21, 2);
lean_inc(x_408);
x_409 = lean_nat_dec_lt(x_407, x_408);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_405)) {
 x_410 = lean_alloc_ctor(0, 2, 0);
} else {
 x_410 = x_405;
}
lean_ctor_set(x_410, 0, x_21);
lean_ctor_set(x_410, 1, x_404);
if (lean_is_scalar(x_403)) {
 x_411 = lean_alloc_ctor(0, 2, 0);
} else {
 x_411 = x_403;
}
lean_ctor_set(x_411, 0, x_402);
lean_ctor_set(x_411, 1, x_410);
x_412 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_412, 0, x_401);
lean_ctor_set(x_412, 1, x_411);
lean_ctor_set(x_17, 1, x_412);
x_413 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_413, 0, x_16);
x_414 = lean_apply_2(x_1, lean_box(0), x_413);
return x_414;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_415 = x_21;
} else {
 lean_dec_ref(x_21);
 x_415 = lean_box(0);
}
x_416 = lean_ctor_get(x_402, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_402, 1);
lean_inc(x_417);
x_418 = lean_ctor_get(x_402, 2);
lean_inc(x_418);
x_419 = lean_unsigned_to_nat(1u);
x_420 = lean_nat_add(x_407, x_419);
lean_inc(x_406);
if (lean_is_scalar(x_415)) {
 x_421 = lean_alloc_ctor(0, 3, 0);
} else {
 x_421 = x_415;
}
lean_ctor_set(x_421, 0, x_406);
lean_ctor_set(x_421, 1, x_420);
lean_ctor_set(x_421, 2, x_408);
x_422 = lean_nat_dec_lt(x_417, x_418);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_405)) {
 x_423 = lean_alloc_ctor(0, 2, 0);
} else {
 x_423 = x_405;
}
lean_ctor_set(x_423, 0, x_421);
lean_ctor_set(x_423, 1, x_404);
if (lean_is_scalar(x_403)) {
 x_424 = lean_alloc_ctor(0, 2, 0);
} else {
 x_424 = x_403;
}
lean_ctor_set(x_424, 0, x_402);
lean_ctor_set(x_424, 1, x_423);
x_425 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_425, 0, x_401);
lean_ctor_set(x_425, 1, x_424);
lean_ctor_set(x_17, 1, x_425);
x_426 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_426, 0, x_16);
x_427 = lean_apply_2(x_1, lean_box(0), x_426);
return x_427;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; 
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 lean_ctor_release(x_402, 2);
 x_428 = x_402;
} else {
 lean_dec_ref(x_402);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_401, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_401, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_401, 2);
lean_inc(x_431);
x_432 = lean_nat_add(x_417, x_419);
lean_inc(x_416);
if (lean_is_scalar(x_428)) {
 x_433 = lean_alloc_ctor(0, 3, 0);
} else {
 x_433 = x_428;
}
lean_ctor_set(x_433, 0, x_416);
lean_ctor_set(x_433, 1, x_432);
lean_ctor_set(x_433, 2, x_418);
x_434 = lean_nat_dec_lt(x_430, x_431);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_431);
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_405)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_405;
}
lean_ctor_set(x_435, 0, x_421);
lean_ctor_set(x_435, 1, x_404);
if (lean_is_scalar(x_403)) {
 x_436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_436 = x_403;
}
lean_ctor_set(x_436, 0, x_433);
lean_ctor_set(x_436, 1, x_435);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_401);
lean_ctor_set(x_437, 1, x_436);
lean_ctor_set(x_17, 1, x_437);
x_438 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_438, 0, x_16);
x_439 = lean_apply_2(x_1, lean_box(0), x_438);
return x_439;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; 
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 lean_ctor_release(x_401, 2);
 x_440 = x_401;
} else {
 lean_dec_ref(x_401);
 x_440 = lean_box(0);
}
x_441 = lean_ctor_get(x_26, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_26, 1);
lean_inc(x_442);
x_443 = lean_ctor_get(x_26, 2);
lean_inc(x_443);
x_444 = lean_nat_add(x_430, x_419);
lean_inc(x_429);
if (lean_is_scalar(x_440)) {
 x_445 = lean_alloc_ctor(0, 3, 0);
} else {
 x_445 = x_440;
}
lean_ctor_set(x_445, 0, x_429);
lean_ctor_set(x_445, 1, x_444);
lean_ctor_set(x_445, 2, x_431);
x_446 = lean_nat_dec_lt(x_442, x_443);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_405)) {
 x_447 = lean_alloc_ctor(0, 2, 0);
} else {
 x_447 = x_405;
}
lean_ctor_set(x_447, 0, x_421);
lean_ctor_set(x_447, 1, x_404);
if (lean_is_scalar(x_403)) {
 x_448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_448 = x_403;
}
lean_ctor_set(x_448, 0, x_433);
lean_ctor_set(x_448, 1, x_447);
x_449 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_449, 0, x_445);
lean_ctor_set(x_449, 1, x_448);
lean_ctor_set(x_17, 1, x_449);
x_450 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_450, 0, x_16);
x_451 = lean_apply_2(x_1, lean_box(0), x_450);
return x_451;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; 
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_452 = x_26;
} else {
 lean_dec_ref(x_26);
 x_452 = lean_box(0);
}
x_453 = lean_ctor_get(x_23, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_23, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_23, 2);
lean_inc(x_455);
x_456 = lean_nat_add(x_442, x_419);
lean_inc(x_441);
if (lean_is_scalar(x_452)) {
 x_457 = lean_alloc_ctor(0, 3, 0);
} else {
 x_457 = x_452;
}
lean_ctor_set(x_457, 0, x_441);
lean_ctor_set(x_457, 1, x_456);
lean_ctor_set(x_457, 2, x_443);
x_458 = lean_nat_dec_lt(x_454, x_455);
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_405)) {
 x_459 = lean_alloc_ctor(0, 2, 0);
} else {
 x_459 = x_405;
}
lean_ctor_set(x_459, 0, x_421);
lean_ctor_set(x_459, 1, x_404);
if (lean_is_scalar(x_403)) {
 x_460 = lean_alloc_ctor(0, 2, 0);
} else {
 x_460 = x_403;
}
lean_ctor_set(x_460, 0, x_433);
lean_ctor_set(x_460, 1, x_459);
x_461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_461, 0, x_445);
lean_ctor_set(x_461, 1, x_460);
lean_ctor_set(x_17, 1, x_461);
lean_ctor_set(x_17, 0, x_457);
x_462 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_462, 0, x_16);
x_463 = lean_apply_2(x_1, lean_box(0), x_462);
return x_463;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
lean_dec(x_405);
lean_dec(x_403);
lean_free_object(x_17);
lean_free_object(x_16);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_464 = x_23;
} else {
 lean_dec_ref(x_23);
 x_464 = lean_box(0);
}
x_465 = lean_array_fget(x_406, x_407);
lean_dec(x_407);
lean_dec(x_406);
x_466 = lean_array_fget(x_416, x_417);
lean_dec(x_417);
lean_dec(x_416);
x_467 = lean_array_fget(x_429, x_430);
lean_dec(x_430);
lean_dec(x_429);
x_468 = lean_array_fget(x_441, x_442);
lean_dec(x_442);
lean_dec(x_441);
x_469 = lean_array_fget(x_453, x_454);
x_470 = lean_box(x_3);
x_471 = lean_box(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_472 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 17, 15);
lean_closure_set(x_472, 0, x_2);
lean_closure_set(x_472, 1, x_470);
lean_closure_set(x_472, 2, x_471);
lean_closure_set(x_472, 3, x_5);
lean_closure_set(x_472, 4, x_6);
lean_closure_set(x_472, 5, x_14);
lean_closure_set(x_472, 6, x_7);
lean_closure_set(x_472, 7, x_469);
lean_closure_set(x_472, 8, x_8);
lean_closure_set(x_472, 9, x_9);
lean_closure_set(x_472, 10, x_10);
lean_closure_set(x_472, 11, x_11);
lean_closure_set(x_472, 12, x_12);
lean_closure_set(x_472, 13, x_467);
lean_closure_set(x_472, 14, x_465);
x_473 = lean_nat_add(x_454, x_419);
lean_dec(x_454);
if (lean_is_scalar(x_464)) {
 x_474 = lean_alloc_ctor(0, 3, 0);
} else {
 x_474 = x_464;
}
lean_ctor_set(x_474, 0, x_453);
lean_ctor_set(x_474, 1, x_473);
lean_ctor_set(x_474, 2, x_455);
lean_inc(x_7);
x_475 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46), 9, 8);
lean_closure_set(x_475, 0, x_404);
lean_closure_set(x_475, 1, x_421);
lean_closure_set(x_475, 2, x_433);
lean_closure_set(x_475, 3, x_445);
lean_closure_set(x_475, 4, x_457);
lean_closure_set(x_475, 5, x_474);
lean_closure_set(x_475, 6, x_1);
lean_closure_set(x_475, 7, x_7);
x_476 = lean_nat_sub(x_468, x_12);
lean_dec(x_12);
lean_dec(x_468);
x_477 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_11, x_10, x_466, x_476, x_13, x_472);
x_478 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_477, x_475);
return x_478;
}
}
}
}
}
}
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; uint8_t x_489; 
x_479 = lean_ctor_get(x_17, 0);
lean_inc(x_479);
lean_dec(x_17);
x_480 = lean_ctor_get(x_18, 0);
lean_inc(x_480);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_481 = x_18;
} else {
 lean_dec_ref(x_18);
 x_481 = lean_box(0);
}
x_482 = lean_ctor_get(x_19, 0);
lean_inc(x_482);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_483 = x_19;
} else {
 lean_dec_ref(x_19);
 x_483 = lean_box(0);
}
x_484 = lean_ctor_get(x_20, 1);
lean_inc(x_484);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_485 = x_20;
} else {
 lean_dec_ref(x_20);
 x_485 = lean_box(0);
}
x_486 = lean_ctor_get(x_21, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_21, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_21, 2);
lean_inc(x_488);
x_489 = lean_nat_dec_lt(x_487, x_488);
if (x_489 == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec(x_488);
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_485)) {
 x_490 = lean_alloc_ctor(0, 2, 0);
} else {
 x_490 = x_485;
}
lean_ctor_set(x_490, 0, x_21);
lean_ctor_set(x_490, 1, x_484);
if (lean_is_scalar(x_483)) {
 x_491 = lean_alloc_ctor(0, 2, 0);
} else {
 x_491 = x_483;
}
lean_ctor_set(x_491, 0, x_482);
lean_ctor_set(x_491, 1, x_490);
if (lean_is_scalar(x_481)) {
 x_492 = lean_alloc_ctor(0, 2, 0);
} else {
 x_492 = x_481;
}
lean_ctor_set(x_492, 0, x_480);
lean_ctor_set(x_492, 1, x_491);
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_479);
lean_ctor_set(x_493, 1, x_492);
lean_ctor_set(x_16, 1, x_493);
x_494 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_494, 0, x_16);
x_495 = lean_apply_2(x_1, lean_box(0), x_494);
return x_495;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_496 = x_21;
} else {
 lean_dec_ref(x_21);
 x_496 = lean_box(0);
}
x_497 = lean_ctor_get(x_482, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_482, 1);
lean_inc(x_498);
x_499 = lean_ctor_get(x_482, 2);
lean_inc(x_499);
x_500 = lean_unsigned_to_nat(1u);
x_501 = lean_nat_add(x_487, x_500);
lean_inc(x_486);
if (lean_is_scalar(x_496)) {
 x_502 = lean_alloc_ctor(0, 3, 0);
} else {
 x_502 = x_496;
}
lean_ctor_set(x_502, 0, x_486);
lean_ctor_set(x_502, 1, x_501);
lean_ctor_set(x_502, 2, x_488);
x_503 = lean_nat_dec_lt(x_498, x_499);
if (x_503 == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
lean_dec(x_499);
lean_dec(x_498);
lean_dec(x_497);
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_485)) {
 x_504 = lean_alloc_ctor(0, 2, 0);
} else {
 x_504 = x_485;
}
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_484);
if (lean_is_scalar(x_483)) {
 x_505 = lean_alloc_ctor(0, 2, 0);
} else {
 x_505 = x_483;
}
lean_ctor_set(x_505, 0, x_482);
lean_ctor_set(x_505, 1, x_504);
if (lean_is_scalar(x_481)) {
 x_506 = lean_alloc_ctor(0, 2, 0);
} else {
 x_506 = x_481;
}
lean_ctor_set(x_506, 0, x_480);
lean_ctor_set(x_506, 1, x_505);
x_507 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_507, 0, x_479);
lean_ctor_set(x_507, 1, x_506);
lean_ctor_set(x_16, 1, x_507);
x_508 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_508, 0, x_16);
x_509 = lean_apply_2(x_1, lean_box(0), x_508);
return x_509;
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; uint8_t x_516; 
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 lean_ctor_release(x_482, 2);
 x_510 = x_482;
} else {
 lean_dec_ref(x_482);
 x_510 = lean_box(0);
}
x_511 = lean_ctor_get(x_480, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_480, 1);
lean_inc(x_512);
x_513 = lean_ctor_get(x_480, 2);
lean_inc(x_513);
x_514 = lean_nat_add(x_498, x_500);
lean_inc(x_497);
if (lean_is_scalar(x_510)) {
 x_515 = lean_alloc_ctor(0, 3, 0);
} else {
 x_515 = x_510;
}
lean_ctor_set(x_515, 0, x_497);
lean_ctor_set(x_515, 1, x_514);
lean_ctor_set(x_515, 2, x_499);
x_516 = lean_nat_dec_lt(x_512, x_513);
if (x_516 == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_498);
lean_dec(x_497);
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_485)) {
 x_517 = lean_alloc_ctor(0, 2, 0);
} else {
 x_517 = x_485;
}
lean_ctor_set(x_517, 0, x_502);
lean_ctor_set(x_517, 1, x_484);
if (lean_is_scalar(x_483)) {
 x_518 = lean_alloc_ctor(0, 2, 0);
} else {
 x_518 = x_483;
}
lean_ctor_set(x_518, 0, x_515);
lean_ctor_set(x_518, 1, x_517);
if (lean_is_scalar(x_481)) {
 x_519 = lean_alloc_ctor(0, 2, 0);
} else {
 x_519 = x_481;
}
lean_ctor_set(x_519, 0, x_480);
lean_ctor_set(x_519, 1, x_518);
x_520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_520, 0, x_479);
lean_ctor_set(x_520, 1, x_519);
lean_ctor_set(x_16, 1, x_520);
x_521 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_521, 0, x_16);
x_522 = lean_apply_2(x_1, lean_box(0), x_521);
return x_522;
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; uint8_t x_529; 
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 lean_ctor_release(x_480, 2);
 x_523 = x_480;
} else {
 lean_dec_ref(x_480);
 x_523 = lean_box(0);
}
x_524 = lean_ctor_get(x_479, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_479, 1);
lean_inc(x_525);
x_526 = lean_ctor_get(x_479, 2);
lean_inc(x_526);
x_527 = lean_nat_add(x_512, x_500);
lean_inc(x_511);
if (lean_is_scalar(x_523)) {
 x_528 = lean_alloc_ctor(0, 3, 0);
} else {
 x_528 = x_523;
}
lean_ctor_set(x_528, 0, x_511);
lean_ctor_set(x_528, 1, x_527);
lean_ctor_set(x_528, 2, x_513);
x_529 = lean_nat_dec_lt(x_525, x_526);
if (x_529 == 0)
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_526);
lean_dec(x_525);
lean_dec(x_524);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_498);
lean_dec(x_497);
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_485)) {
 x_530 = lean_alloc_ctor(0, 2, 0);
} else {
 x_530 = x_485;
}
lean_ctor_set(x_530, 0, x_502);
lean_ctor_set(x_530, 1, x_484);
if (lean_is_scalar(x_483)) {
 x_531 = lean_alloc_ctor(0, 2, 0);
} else {
 x_531 = x_483;
}
lean_ctor_set(x_531, 0, x_515);
lean_ctor_set(x_531, 1, x_530);
if (lean_is_scalar(x_481)) {
 x_532 = lean_alloc_ctor(0, 2, 0);
} else {
 x_532 = x_481;
}
lean_ctor_set(x_532, 0, x_528);
lean_ctor_set(x_532, 1, x_531);
x_533 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_533, 0, x_479);
lean_ctor_set(x_533, 1, x_532);
lean_ctor_set(x_16, 1, x_533);
x_534 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_534, 0, x_16);
x_535 = lean_apply_2(x_1, lean_box(0), x_534);
return x_535;
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; 
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 lean_ctor_release(x_479, 1);
 lean_ctor_release(x_479, 2);
 x_536 = x_479;
} else {
 lean_dec_ref(x_479);
 x_536 = lean_box(0);
}
x_537 = lean_ctor_get(x_23, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_23, 1);
lean_inc(x_538);
x_539 = lean_ctor_get(x_23, 2);
lean_inc(x_539);
x_540 = lean_nat_add(x_525, x_500);
lean_inc(x_524);
if (lean_is_scalar(x_536)) {
 x_541 = lean_alloc_ctor(0, 3, 0);
} else {
 x_541 = x_536;
}
lean_ctor_set(x_541, 0, x_524);
lean_ctor_set(x_541, 1, x_540);
lean_ctor_set(x_541, 2, x_526);
x_542 = lean_nat_dec_lt(x_538, x_539);
if (x_542 == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_525);
lean_dec(x_524);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_498);
lean_dec(x_497);
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_485)) {
 x_543 = lean_alloc_ctor(0, 2, 0);
} else {
 x_543 = x_485;
}
lean_ctor_set(x_543, 0, x_502);
lean_ctor_set(x_543, 1, x_484);
if (lean_is_scalar(x_483)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_483;
}
lean_ctor_set(x_544, 0, x_515);
lean_ctor_set(x_544, 1, x_543);
if (lean_is_scalar(x_481)) {
 x_545 = lean_alloc_ctor(0, 2, 0);
} else {
 x_545 = x_481;
}
lean_ctor_set(x_545, 0, x_528);
lean_ctor_set(x_545, 1, x_544);
x_546 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_546, 0, x_541);
lean_ctor_set(x_546, 1, x_545);
lean_ctor_set(x_16, 1, x_546);
x_547 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_547, 0, x_16);
x_548 = lean_apply_2(x_1, lean_box(0), x_547);
return x_548;
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_485);
lean_dec(x_483);
lean_dec(x_481);
lean_free_object(x_16);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_549 = x_23;
} else {
 lean_dec_ref(x_23);
 x_549 = lean_box(0);
}
x_550 = lean_array_fget(x_486, x_487);
lean_dec(x_487);
lean_dec(x_486);
x_551 = lean_array_fget(x_497, x_498);
lean_dec(x_498);
lean_dec(x_497);
x_552 = lean_array_fget(x_511, x_512);
lean_dec(x_512);
lean_dec(x_511);
x_553 = lean_array_fget(x_524, x_525);
lean_dec(x_525);
lean_dec(x_524);
x_554 = lean_array_fget(x_537, x_538);
x_555 = lean_box(x_3);
x_556 = lean_box(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_557 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 17, 15);
lean_closure_set(x_557, 0, x_2);
lean_closure_set(x_557, 1, x_555);
lean_closure_set(x_557, 2, x_556);
lean_closure_set(x_557, 3, x_5);
lean_closure_set(x_557, 4, x_6);
lean_closure_set(x_557, 5, x_14);
lean_closure_set(x_557, 6, x_7);
lean_closure_set(x_557, 7, x_554);
lean_closure_set(x_557, 8, x_8);
lean_closure_set(x_557, 9, x_9);
lean_closure_set(x_557, 10, x_10);
lean_closure_set(x_557, 11, x_11);
lean_closure_set(x_557, 12, x_12);
lean_closure_set(x_557, 13, x_552);
lean_closure_set(x_557, 14, x_550);
x_558 = lean_nat_add(x_538, x_500);
lean_dec(x_538);
if (lean_is_scalar(x_549)) {
 x_559 = lean_alloc_ctor(0, 3, 0);
} else {
 x_559 = x_549;
}
lean_ctor_set(x_559, 0, x_537);
lean_ctor_set(x_559, 1, x_558);
lean_ctor_set(x_559, 2, x_539);
lean_inc(x_7);
x_560 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46), 9, 8);
lean_closure_set(x_560, 0, x_484);
lean_closure_set(x_560, 1, x_502);
lean_closure_set(x_560, 2, x_515);
lean_closure_set(x_560, 3, x_528);
lean_closure_set(x_560, 4, x_541);
lean_closure_set(x_560, 5, x_559);
lean_closure_set(x_560, 6, x_1);
lean_closure_set(x_560, 7, x_7);
x_561 = lean_nat_sub(x_553, x_12);
lean_dec(x_12);
lean_dec(x_553);
x_562 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_11, x_10, x_551, x_561, x_13, x_557);
x_563 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_562, x_560);
return x_563;
}
}
}
}
}
}
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; 
x_564 = lean_ctor_get(x_16, 0);
lean_inc(x_564);
lean_dec(x_16);
x_565 = lean_ctor_get(x_17, 0);
lean_inc(x_565);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_566 = x_17;
} else {
 lean_dec_ref(x_17);
 x_566 = lean_box(0);
}
x_567 = lean_ctor_get(x_18, 0);
lean_inc(x_567);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_568 = x_18;
} else {
 lean_dec_ref(x_18);
 x_568 = lean_box(0);
}
x_569 = lean_ctor_get(x_19, 0);
lean_inc(x_569);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_570 = x_19;
} else {
 lean_dec_ref(x_19);
 x_570 = lean_box(0);
}
x_571 = lean_ctor_get(x_20, 1);
lean_inc(x_571);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_572 = x_20;
} else {
 lean_dec_ref(x_20);
 x_572 = lean_box(0);
}
x_573 = lean_ctor_get(x_21, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_21, 1);
lean_inc(x_574);
x_575 = lean_ctor_get(x_21, 2);
lean_inc(x_575);
x_576 = lean_nat_dec_lt(x_574, x_575);
if (x_576 == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
lean_dec(x_575);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_572)) {
 x_577 = lean_alloc_ctor(0, 2, 0);
} else {
 x_577 = x_572;
}
lean_ctor_set(x_577, 0, x_21);
lean_ctor_set(x_577, 1, x_571);
if (lean_is_scalar(x_570)) {
 x_578 = lean_alloc_ctor(0, 2, 0);
} else {
 x_578 = x_570;
}
lean_ctor_set(x_578, 0, x_569);
lean_ctor_set(x_578, 1, x_577);
if (lean_is_scalar(x_568)) {
 x_579 = lean_alloc_ctor(0, 2, 0);
} else {
 x_579 = x_568;
}
lean_ctor_set(x_579, 0, x_567);
lean_ctor_set(x_579, 1, x_578);
if (lean_is_scalar(x_566)) {
 x_580 = lean_alloc_ctor(0, 2, 0);
} else {
 x_580 = x_566;
}
lean_ctor_set(x_580, 0, x_565);
lean_ctor_set(x_580, 1, x_579);
x_581 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_581, 0, x_564);
lean_ctor_set(x_581, 1, x_580);
x_582 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_582, 0, x_581);
x_583 = lean_apply_2(x_1, lean_box(0), x_582);
return x_583;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_584 = x_21;
} else {
 lean_dec_ref(x_21);
 x_584 = lean_box(0);
}
x_585 = lean_ctor_get(x_569, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_569, 1);
lean_inc(x_586);
x_587 = lean_ctor_get(x_569, 2);
lean_inc(x_587);
x_588 = lean_unsigned_to_nat(1u);
x_589 = lean_nat_add(x_574, x_588);
lean_inc(x_573);
if (lean_is_scalar(x_584)) {
 x_590 = lean_alloc_ctor(0, 3, 0);
} else {
 x_590 = x_584;
}
lean_ctor_set(x_590, 0, x_573);
lean_ctor_set(x_590, 1, x_589);
lean_ctor_set(x_590, 2, x_575);
x_591 = lean_nat_dec_lt(x_586, x_587);
if (x_591 == 0)
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
lean_dec(x_587);
lean_dec(x_586);
lean_dec(x_585);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_572)) {
 x_592 = lean_alloc_ctor(0, 2, 0);
} else {
 x_592 = x_572;
}
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_571);
if (lean_is_scalar(x_570)) {
 x_593 = lean_alloc_ctor(0, 2, 0);
} else {
 x_593 = x_570;
}
lean_ctor_set(x_593, 0, x_569);
lean_ctor_set(x_593, 1, x_592);
if (lean_is_scalar(x_568)) {
 x_594 = lean_alloc_ctor(0, 2, 0);
} else {
 x_594 = x_568;
}
lean_ctor_set(x_594, 0, x_567);
lean_ctor_set(x_594, 1, x_593);
if (lean_is_scalar(x_566)) {
 x_595 = lean_alloc_ctor(0, 2, 0);
} else {
 x_595 = x_566;
}
lean_ctor_set(x_595, 0, x_565);
lean_ctor_set(x_595, 1, x_594);
x_596 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_596, 0, x_564);
lean_ctor_set(x_596, 1, x_595);
x_597 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_597, 0, x_596);
x_598 = lean_apply_2(x_1, lean_box(0), x_597);
return x_598;
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; uint8_t x_605; 
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 lean_ctor_release(x_569, 2);
 x_599 = x_569;
} else {
 lean_dec_ref(x_569);
 x_599 = lean_box(0);
}
x_600 = lean_ctor_get(x_567, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_567, 1);
lean_inc(x_601);
x_602 = lean_ctor_get(x_567, 2);
lean_inc(x_602);
x_603 = lean_nat_add(x_586, x_588);
lean_inc(x_585);
if (lean_is_scalar(x_599)) {
 x_604 = lean_alloc_ctor(0, 3, 0);
} else {
 x_604 = x_599;
}
lean_ctor_set(x_604, 0, x_585);
lean_ctor_set(x_604, 1, x_603);
lean_ctor_set(x_604, 2, x_587);
x_605 = lean_nat_dec_lt(x_601, x_602);
if (x_605 == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec(x_602);
lean_dec(x_601);
lean_dec(x_600);
lean_dec(x_586);
lean_dec(x_585);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_572)) {
 x_606 = lean_alloc_ctor(0, 2, 0);
} else {
 x_606 = x_572;
}
lean_ctor_set(x_606, 0, x_590);
lean_ctor_set(x_606, 1, x_571);
if (lean_is_scalar(x_570)) {
 x_607 = lean_alloc_ctor(0, 2, 0);
} else {
 x_607 = x_570;
}
lean_ctor_set(x_607, 0, x_604);
lean_ctor_set(x_607, 1, x_606);
if (lean_is_scalar(x_568)) {
 x_608 = lean_alloc_ctor(0, 2, 0);
} else {
 x_608 = x_568;
}
lean_ctor_set(x_608, 0, x_567);
lean_ctor_set(x_608, 1, x_607);
if (lean_is_scalar(x_566)) {
 x_609 = lean_alloc_ctor(0, 2, 0);
} else {
 x_609 = x_566;
}
lean_ctor_set(x_609, 0, x_565);
lean_ctor_set(x_609, 1, x_608);
x_610 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_610, 0, x_564);
lean_ctor_set(x_610, 1, x_609);
x_611 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_611, 0, x_610);
x_612 = lean_apply_2(x_1, lean_box(0), x_611);
return x_612;
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; uint8_t x_619; 
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 lean_ctor_release(x_567, 1);
 lean_ctor_release(x_567, 2);
 x_613 = x_567;
} else {
 lean_dec_ref(x_567);
 x_613 = lean_box(0);
}
x_614 = lean_ctor_get(x_565, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_565, 1);
lean_inc(x_615);
x_616 = lean_ctor_get(x_565, 2);
lean_inc(x_616);
x_617 = lean_nat_add(x_601, x_588);
lean_inc(x_600);
if (lean_is_scalar(x_613)) {
 x_618 = lean_alloc_ctor(0, 3, 0);
} else {
 x_618 = x_613;
}
lean_ctor_set(x_618, 0, x_600);
lean_ctor_set(x_618, 1, x_617);
lean_ctor_set(x_618, 2, x_602);
x_619 = lean_nat_dec_lt(x_615, x_616);
if (x_619 == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; 
lean_dec(x_616);
lean_dec(x_615);
lean_dec(x_614);
lean_dec(x_601);
lean_dec(x_600);
lean_dec(x_586);
lean_dec(x_585);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_572)) {
 x_620 = lean_alloc_ctor(0, 2, 0);
} else {
 x_620 = x_572;
}
lean_ctor_set(x_620, 0, x_590);
lean_ctor_set(x_620, 1, x_571);
if (lean_is_scalar(x_570)) {
 x_621 = lean_alloc_ctor(0, 2, 0);
} else {
 x_621 = x_570;
}
lean_ctor_set(x_621, 0, x_604);
lean_ctor_set(x_621, 1, x_620);
if (lean_is_scalar(x_568)) {
 x_622 = lean_alloc_ctor(0, 2, 0);
} else {
 x_622 = x_568;
}
lean_ctor_set(x_622, 0, x_618);
lean_ctor_set(x_622, 1, x_621);
if (lean_is_scalar(x_566)) {
 x_623 = lean_alloc_ctor(0, 2, 0);
} else {
 x_623 = x_566;
}
lean_ctor_set(x_623, 0, x_565);
lean_ctor_set(x_623, 1, x_622);
x_624 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_624, 0, x_564);
lean_ctor_set(x_624, 1, x_623);
x_625 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_625, 0, x_624);
x_626 = lean_apply_2(x_1, lean_box(0), x_625);
return x_626;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; uint8_t x_633; 
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 lean_ctor_release(x_565, 1);
 lean_ctor_release(x_565, 2);
 x_627 = x_565;
} else {
 lean_dec_ref(x_565);
 x_627 = lean_box(0);
}
x_628 = lean_ctor_get(x_564, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_564, 1);
lean_inc(x_629);
x_630 = lean_ctor_get(x_564, 2);
lean_inc(x_630);
x_631 = lean_nat_add(x_615, x_588);
lean_inc(x_614);
if (lean_is_scalar(x_627)) {
 x_632 = lean_alloc_ctor(0, 3, 0);
} else {
 x_632 = x_627;
}
lean_ctor_set(x_632, 0, x_614);
lean_ctor_set(x_632, 1, x_631);
lean_ctor_set(x_632, 2, x_616);
x_633 = lean_nat_dec_lt(x_629, x_630);
if (x_633 == 0)
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; 
lean_dec(x_630);
lean_dec(x_629);
lean_dec(x_628);
lean_dec(x_615);
lean_dec(x_614);
lean_dec(x_601);
lean_dec(x_600);
lean_dec(x_586);
lean_dec(x_585);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_572)) {
 x_634 = lean_alloc_ctor(0, 2, 0);
} else {
 x_634 = x_572;
}
lean_ctor_set(x_634, 0, x_590);
lean_ctor_set(x_634, 1, x_571);
if (lean_is_scalar(x_570)) {
 x_635 = lean_alloc_ctor(0, 2, 0);
} else {
 x_635 = x_570;
}
lean_ctor_set(x_635, 0, x_604);
lean_ctor_set(x_635, 1, x_634);
if (lean_is_scalar(x_568)) {
 x_636 = lean_alloc_ctor(0, 2, 0);
} else {
 x_636 = x_568;
}
lean_ctor_set(x_636, 0, x_618);
lean_ctor_set(x_636, 1, x_635);
if (lean_is_scalar(x_566)) {
 x_637 = lean_alloc_ctor(0, 2, 0);
} else {
 x_637 = x_566;
}
lean_ctor_set(x_637, 0, x_632);
lean_ctor_set(x_637, 1, x_636);
x_638 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_638, 0, x_564);
lean_ctor_set(x_638, 1, x_637);
x_639 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_639, 0, x_638);
x_640 = lean_apply_2(x_1, lean_box(0), x_639);
return x_640;
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
lean_dec(x_572);
lean_dec(x_570);
lean_dec(x_568);
lean_dec(x_566);
if (lean_is_exclusive(x_564)) {
 lean_ctor_release(x_564, 0);
 lean_ctor_release(x_564, 1);
 lean_ctor_release(x_564, 2);
 x_641 = x_564;
} else {
 lean_dec_ref(x_564);
 x_641 = lean_box(0);
}
x_642 = lean_array_fget(x_573, x_574);
lean_dec(x_574);
lean_dec(x_573);
x_643 = lean_array_fget(x_585, x_586);
lean_dec(x_586);
lean_dec(x_585);
x_644 = lean_array_fget(x_600, x_601);
lean_dec(x_601);
lean_dec(x_600);
x_645 = lean_array_fget(x_614, x_615);
lean_dec(x_615);
lean_dec(x_614);
x_646 = lean_array_fget(x_628, x_629);
x_647 = lean_box(x_3);
x_648 = lean_box(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_649 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 17, 15);
lean_closure_set(x_649, 0, x_2);
lean_closure_set(x_649, 1, x_647);
lean_closure_set(x_649, 2, x_648);
lean_closure_set(x_649, 3, x_5);
lean_closure_set(x_649, 4, x_6);
lean_closure_set(x_649, 5, x_14);
lean_closure_set(x_649, 6, x_7);
lean_closure_set(x_649, 7, x_646);
lean_closure_set(x_649, 8, x_8);
lean_closure_set(x_649, 9, x_9);
lean_closure_set(x_649, 10, x_10);
lean_closure_set(x_649, 11, x_11);
lean_closure_set(x_649, 12, x_12);
lean_closure_set(x_649, 13, x_644);
lean_closure_set(x_649, 14, x_642);
x_650 = lean_nat_add(x_629, x_588);
lean_dec(x_629);
if (lean_is_scalar(x_641)) {
 x_651 = lean_alloc_ctor(0, 3, 0);
} else {
 x_651 = x_641;
}
lean_ctor_set(x_651, 0, x_628);
lean_ctor_set(x_651, 1, x_650);
lean_ctor_set(x_651, 2, x_630);
lean_inc(x_7);
x_652 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46), 9, 8);
lean_closure_set(x_652, 0, x_571);
lean_closure_set(x_652, 1, x_590);
lean_closure_set(x_652, 2, x_604);
lean_closure_set(x_652, 3, x_618);
lean_closure_set(x_652, 4, x_632);
lean_closure_set(x_652, 5, x_651);
lean_closure_set(x_652, 6, x_1);
lean_closure_set(x_652, 7, x_7);
x_653 = lean_nat_sub(x_645, x_12);
lean_dec(x_12);
lean_dec(x_645);
x_654 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(x_11, x_10, x_643, x_653, x_13, x_649);
x_655 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_654, x_652);
return x_655;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = l_Array_append___redArg(x_1, x_13);
x_15 = l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__9;
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
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
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed), 13, 12);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Array_toSubarray___redArg(x_1, x_2, x_3);
x_14 = lean_array_get_size(x_4);
lean_inc(x_2);
x_15 = l_Array_toSubarray___redArg(x_4, x_2, x_14);
x_16 = lean_array_get_size(x_5);
lean_inc(x_2);
x_17 = l_Array_toSubarray___redArg(x_5, x_2, x_16);
x_18 = lean_array_get_size(x_6);
lean_inc(x_2);
x_19 = l_Array_toSubarray___redArg(x_6, x_2, x_18);
x_20 = lean_array_get_size(x_12);
lean_inc(x_2);
x_21 = l_Array_toSubarray___redArg(x_12, x_2, x_20);
x_22 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_7);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Std_Range_forIn_x27_loop___redArg(x_8, x_23, x_9, x_28, x_2);
x_30 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_29, x_11);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25) {
_start:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc(x_13);
lean_inc(x_1);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48), 15, 14);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_1);
lean_closure_set(x_26, 2, x_2);
lean_closure_set(x_26, 3, x_3);
lean_closure_set(x_26, 4, x_4);
lean_closure_set(x_26, 5, x_5);
lean_closure_set(x_26, 6, x_6);
lean_closure_set(x_26, 7, x_7);
lean_closure_set(x_26, 8, x_8);
lean_closure_set(x_26, 9, x_9);
lean_closure_set(x_26, 10, x_10);
lean_closure_set(x_26, 11, x_11);
lean_closure_set(x_26, 12, x_12);
lean_closure_set(x_26, 13, x_13);
lean_inc(x_13);
lean_inc(x_16);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 12, 11);
lean_closure_set(x_27, 0, x_14);
lean_closure_set(x_27, 1, x_15);
lean_closure_set(x_27, 2, x_16);
lean_closure_set(x_27, 3, x_17);
lean_closure_set(x_27, 4, x_1);
lean_closure_set(x_27, 5, x_18);
lean_closure_set(x_27, 6, x_19);
lean_closure_set(x_27, 7, x_20);
lean_closure_set(x_27, 8, x_21);
lean_closure_set(x_27, 9, x_13);
lean_closure_set(x_27, 10, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN), 7, 2);
lean_closure_set(x_28, 0, x_16);
lean_closure_set(x_28, 1, x_22);
x_29 = lean_apply_2(x_23, lean_box(0), x_28);
x_30 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_29, x_27);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_3, lean_box(0), x_1);
x_10 = l_Lean_Meta_mapErrorImp___redArg(x_9, x_2, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to transform matcher, type error when constructing splitter motive:", 74, 74);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nfailed with", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
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
x_12 = l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1;
lean_inc(x_2);
x_13 = l_Lean_indentExpr(x_2);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
x_14 = l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_check), 6, 1);
lean_closure_set(x_17, 0, x_2);
x_18 = lean_apply_2(x_3, lean_box(0), x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53), 8, 2);
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
x_26 = l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1;
lean_inc(x_2);
x_27 = l_Lean_indentExpr(x_2);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54), 2, 1);
lean_closure_set(x_31, 0, x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_Meta_check), 6, 1);
lean_closure_set(x_32, 0, x_2);
x_33 = lean_apply_2(x_3, lean_box(0), x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53), 8, 2);
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
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_box(0);
x_40 = lean_apply_2(x_6, lean_box(0), x_39);
x_41 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_40, x_7);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24) {
_start:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_25);
x_27 = l_Lean_Expr_const___override(x_25, x_1);
x_28 = l_Lean_mkAppN(x_27, x_2);
lean_inc(x_3);
x_29 = l_Lean_Expr_app___override(x_28, x_3);
x_30 = l_Lean_mkAppN(x_29, x_4);
lean_inc(x_21);
lean_inc(x_30);
lean_inc(x_12);
lean_inc(x_9);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed), 25, 23);
lean_closure_set(x_31, 0, x_26);
lean_closure_set(x_31, 1, x_5);
lean_closure_set(x_31, 2, x_25);
lean_closure_set(x_31, 3, x_6);
lean_closure_set(x_31, 4, x_7);
lean_closure_set(x_31, 5, x_8);
lean_closure_set(x_31, 6, x_2);
lean_closure_set(x_31, 7, x_3);
lean_closure_set(x_31, 8, x_4);
lean_closure_set(x_31, 9, x_9);
lean_closure_set(x_31, 10, x_10);
lean_closure_set(x_31, 11, x_11);
lean_closure_set(x_31, 12, x_12);
lean_closure_set(x_31, 13, x_13);
lean_closure_set(x_31, 14, x_14);
lean_closure_set(x_31, 15, x_15);
lean_closure_set(x_31, 16, x_16);
lean_closure_set(x_31, 17, x_17);
lean_closure_set(x_31, 18, x_18);
lean_closure_set(x_31, 19, x_19);
lean_closure_set(x_31, 20, x_20);
lean_closure_set(x_31, 21, x_30);
lean_closure_set(x_31, 22, x_21);
x_32 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__52), 3, 2);
lean_closure_set(x_32, 0, x_31);
lean_closure_set(x_32, 1, x_22);
lean_inc(x_32);
lean_inc(x_12);
lean_inc(x_21);
lean_inc(x_30);
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed), 8, 7);
lean_closure_set(x_33, 0, x_23);
lean_closure_set(x_33, 1, x_30);
lean_closure_set(x_33, 2, x_21);
lean_closure_set(x_33, 3, x_12);
lean_closure_set(x_33, 4, x_32);
lean_closure_set(x_33, 5, x_9);
lean_closure_set(x_33, 6, x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_isTypeCorrect), 6, 1);
lean_closure_set(x_34, 0, x_30);
x_35 = lean_apply_2(x_21, lean_box(0), x_34);
x_36 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_35, x_33);
return x_36;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24) {
_start:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_inc(x_20);
lean_inc(x_12);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56___boxed), 24, 23);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_2);
lean_closure_set(x_25, 2, x_3);
lean_closure_set(x_25, 3, x_4);
lean_closure_set(x_25, 4, x_5);
lean_closure_set(x_25, 5, x_6);
lean_closure_set(x_25, 6, x_7);
lean_closure_set(x_25, 7, x_8);
lean_closure_set(x_25, 8, x_9);
lean_closure_set(x_25, 9, x_10);
lean_closure_set(x_25, 10, x_11);
lean_closure_set(x_25, 11, x_12);
lean_closure_set(x_25, 12, x_13);
lean_closure_set(x_25, 13, x_14);
lean_closure_set(x_25, 14, x_15);
lean_closure_set(x_25, 15, x_16);
lean_closure_set(x_25, 16, x_24);
lean_closure_set(x_25, 17, x_17);
lean_closure_set(x_25, 18, x_18);
lean_closure_set(x_25, 19, x_19);
lean_closure_set(x_25, 20, x_20);
lean_closure_set(x_25, 21, x_21);
lean_closure_set(x_25, 22, x_22);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_Match_getEquationsFor___boxed), 6, 1);
lean_closure_set(x_26, 0, x_23);
x_27 = lean_apply_2(x_20, lean_box(0), x_26);
x_28 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_27, x_25);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24) {
_start:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_array_get_size(x_1);
lean_inc(x_19);
lean_inc(x_25);
lean_inc(x_13);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed), 24, 23);
lean_closure_set(x_26, 0, x_2);
lean_closure_set(x_26, 1, x_3);
lean_closure_set(x_26, 2, x_4);
lean_closure_set(x_26, 3, x_5);
lean_closure_set(x_26, 4, x_6);
lean_closure_set(x_26, 5, x_7);
lean_closure_set(x_26, 6, x_8);
lean_closure_set(x_26, 7, x_9);
lean_closure_set(x_26, 8, x_10);
lean_closure_set(x_26, 9, x_11);
lean_closure_set(x_26, 10, x_12);
lean_closure_set(x_26, 11, x_13);
lean_closure_set(x_26, 12, x_1);
lean_closure_set(x_26, 13, x_14);
lean_closure_set(x_26, 14, x_25);
lean_closure_set(x_26, 15, x_15);
lean_closure_set(x_26, 16, x_16);
lean_closure_set(x_26, 17, x_17);
lean_closure_set(x_26, 18, x_18);
lean_closure_set(x_26, 19, x_19);
lean_closure_set(x_26, 20, x_23);
lean_closure_set(x_26, 21, x_20);
lean_closure_set(x_26, 22, x_21);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN), 7, 2);
lean_closure_set(x_27, 0, x_25);
lean_closure_set(x_27, 1, x_22);
x_28 = lean_apply_2(x_19, lean_box(0), x_27);
x_29 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_28, x_26);
return x_29;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to transform matcher, type error when constructing new pre-splitter motive:", 82, 82);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
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
x_12 = l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1;
lean_inc(x_2);
x_13 = l_Lean_indentExpr(x_2);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
x_14 = l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_check), 6, 1);
lean_closure_set(x_17, 0, x_2);
x_18 = lean_apply_2(x_3, lean_box(0), x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53), 8, 2);
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
x_26 = l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1;
lean_inc(x_2);
x_27 = l_Lean_indentExpr(x_2);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54), 2, 1);
lean_closure_set(x_31, 0, x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_Meta_check), 6, 1);
lean_closure_set(x_32, 0, x_2);
x_33 = lean_apply_2(x_3, lean_box(0), x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53), 8, 2);
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
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_box(0);
x_40 = lean_apply_2(x_6, lean_box(0), x_39);
x_41 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_40, x_7);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, uint8_t x_25, uint8_t x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30) {
_start:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed), 2, 1);
lean_closure_set(x_34, 0, x_32);
if (x_25 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
goto block_50;
}
else
{
if (x_26 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_8);
x_51 = lean_box(x_2);
x_52 = lean_box(x_25);
lean_inc(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_53 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed), 16, 13);
lean_closure_set(x_53, 0, x_1);
lean_closure_set(x_53, 1, x_27);
lean_closure_set(x_53, 2, x_51);
lean_closure_set(x_53, 3, x_52);
lean_closure_set(x_53, 4, x_3);
lean_closure_set(x_53, 5, x_4);
lean_closure_set(x_53, 6, x_5);
lean_closure_set(x_53, 7, x_28);
lean_closure_set(x_53, 8, x_32);
lean_closure_set(x_53, 9, x_6);
lean_closure_set(x_53, 10, x_7);
lean_closure_set(x_53, 11, x_29);
lean_closure_set(x_53, 12, x_20);
lean_inc(x_9);
x_54 = lean_array_to_list(x_9);
lean_inc(x_54);
lean_inc(x_10);
x_55 = l_Lean_Expr_const___override(x_10, x_54);
x_56 = l_Lean_mkAppN(x_55, x_11);
lean_inc(x_12);
x_57 = l_Lean_Expr_app___override(x_56, x_12);
x_58 = l_Lean_mkAppN(x_57, x_13);
lean_inc(x_58);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_5);
lean_inc(x_1);
x_59 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed), 24, 22);
lean_closure_set(x_59, 0, x_19);
lean_closure_set(x_59, 1, x_54);
lean_closure_set(x_59, 2, x_11);
lean_closure_set(x_59, 3, x_12);
lean_closure_set(x_59, 4, x_13);
lean_closure_set(x_59, 5, x_34);
lean_closure_set(x_59, 6, x_9);
lean_closure_set(x_59, 7, x_15);
lean_closure_set(x_59, 8, x_16);
lean_closure_set(x_59, 9, x_1);
lean_closure_set(x_59, 10, x_17);
lean_closure_set(x_59, 11, x_18);
lean_closure_set(x_59, 12, x_5);
lean_closure_set(x_59, 13, x_20);
lean_closure_set(x_59, 14, x_14);
lean_closure_set(x_59, 15, x_21);
lean_closure_set(x_59, 16, x_7);
lean_closure_set(x_59, 17, x_53);
lean_closure_set(x_59, 18, x_3);
lean_closure_set(x_59, 19, x_6);
lean_closure_set(x_59, 20, x_10);
lean_closure_set(x_59, 21, x_58);
x_60 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35), 3, 2);
lean_closure_set(x_60, 0, x_59);
lean_closure_set(x_60, 1, x_33);
lean_inc(x_60);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_58);
x_61 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed), 8, 7);
lean_closure_set(x_61, 0, x_6);
lean_closure_set(x_61, 1, x_58);
lean_closure_set(x_61, 2, x_3);
lean_closure_set(x_61, 3, x_5);
lean_closure_set(x_61, 4, x_60);
lean_closure_set(x_61, 5, x_1);
lean_closure_set(x_61, 6, x_60);
x_62 = lean_alloc_closure((void*)(l_Lean_Meta_isTypeCorrect), 6, 1);
lean_closure_set(x_62, 0, x_58);
x_63 = lean_apply_2(x_3, lean_box(0), x_62);
x_64 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_63, x_61);
return x_64;
}
else
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
goto block_50;
}
}
block_50:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_35 = lean_box(1);
x_36 = lean_box(x_2);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_37 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__30___boxed), 13, 10);
lean_closure_set(x_37, 0, x_1);
lean_closure_set(x_37, 1, x_36);
lean_closure_set(x_37, 2, x_35);
lean_closure_set(x_37, 3, x_3);
lean_closure_set(x_37, 4, x_4);
lean_closure_set(x_37, 5, x_5);
lean_closure_set(x_37, 6, x_6);
lean_closure_set(x_37, 7, x_7);
lean_closure_set(x_37, 8, x_8);
lean_closure_set(x_37, 9, x_32);
lean_inc(x_9);
x_38 = lean_array_to_list(x_9);
lean_inc(x_10);
x_39 = l_Lean_Expr_const___override(x_10, x_38);
x_40 = l_Lean_mkAppN(x_39, x_11);
lean_inc(x_12);
x_41 = l_Lean_Expr_app___override(x_40, x_12);
x_42 = l_Lean_mkAppN(x_41, x_13);
lean_inc(x_3);
lean_inc(x_42);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_1);
x_43 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed), 22, 20);
lean_closure_set(x_43, 0, x_14);
lean_closure_set(x_43, 1, x_34);
lean_closure_set(x_43, 2, x_10);
lean_closure_set(x_43, 3, x_9);
lean_closure_set(x_43, 4, x_15);
lean_closure_set(x_43, 5, x_16);
lean_closure_set(x_43, 6, x_11);
lean_closure_set(x_43, 7, x_12);
lean_closure_set(x_43, 8, x_13);
lean_closure_set(x_43, 9, x_1);
lean_closure_set(x_43, 10, x_17);
lean_closure_set(x_43, 11, x_18);
lean_closure_set(x_43, 12, x_5);
lean_closure_set(x_43, 13, x_19);
lean_closure_set(x_43, 14, x_20);
lean_closure_set(x_43, 15, x_21);
lean_closure_set(x_43, 16, x_7);
lean_closure_set(x_43, 17, x_37);
lean_closure_set(x_43, 18, x_42);
lean_closure_set(x_43, 19, x_3);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35), 3, 2);
lean_closure_set(x_44, 0, x_43);
lean_closure_set(x_44, 1, x_33);
lean_inc(x_44);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_42);
x_45 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed), 5, 4);
lean_closure_set(x_45, 0, x_42);
lean_closure_set(x_45, 1, x_3);
lean_closure_set(x_45, 2, x_5);
lean_closure_set(x_45, 3, x_44);
lean_inc(x_5);
lean_inc(x_42);
x_46 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed), 10, 9);
lean_closure_set(x_46, 0, x_42);
lean_closure_set(x_46, 1, x_7);
lean_closure_set(x_46, 2, x_22);
lean_closure_set(x_46, 3, x_23);
lean_closure_set(x_46, 4, x_24);
lean_closure_set(x_46, 5, x_5);
lean_closure_set(x_46, 6, x_45);
lean_closure_set(x_46, 7, x_1);
lean_closure_set(x_46, 8, x_44);
x_47 = lean_alloc_closure((void*)(l_Lean_Meta_isTypeCorrect), 6, 1);
lean_closure_set(x_47, 0, x_42);
x_48 = lean_apply_2(x_3, lean_box(0), x_47);
x_49 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_48, x_46);
return x_49;
}
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, uint8_t x_22, uint8_t x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29) {
_start:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__0;
x_32 = lean_box(x_2);
x_33 = lean_box(x_22);
x_34 = lean_box(x_23);
lean_inc(x_12);
lean_inc(x_7);
lean_inc(x_5);
x_35 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed), 30, 29);
lean_closure_set(x_35, 0, x_1);
lean_closure_set(x_35, 1, x_32);
lean_closure_set(x_35, 2, x_3);
lean_closure_set(x_35, 3, x_4);
lean_closure_set(x_35, 4, x_5);
lean_closure_set(x_35, 5, x_6);
lean_closure_set(x_35, 6, x_7);
lean_closure_set(x_35, 7, x_8);
lean_closure_set(x_35, 8, x_29);
lean_closure_set(x_35, 9, x_9);
lean_closure_set(x_35, 10, x_10);
lean_closure_set(x_35, 11, x_11);
lean_closure_set(x_35, 12, x_12);
lean_closure_set(x_35, 13, x_13);
lean_closure_set(x_35, 14, x_14);
lean_closure_set(x_35, 15, x_15);
lean_closure_set(x_35, 16, x_16);
lean_closure_set(x_35, 17, x_17);
lean_closure_set(x_35, 18, x_18);
lean_closure_set(x_35, 19, x_30);
lean_closure_set(x_35, 20, x_31);
lean_closure_set(x_35, 21, x_19);
lean_closure_set(x_35, 22, x_20);
lean_closure_set(x_35, 23, x_21);
lean_closure_set(x_35, 24, x_33);
lean_closure_set(x_35, 25, x_34);
lean_closure_set(x_35, 26, x_24);
lean_closure_set(x_35, 27, x_25);
lean_closure_set(x_35, 28, x_26);
x_36 = l_Array_reverse___redArg(x_27);
x_37 = lean_array_get_size(x_36);
x_38 = l_Array_toSubarray___redArg(x_36, x_30, x_37);
x_39 = l_Array_reverse___redArg(x_12);
x_40 = l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__1;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_array_size(x_39);
x_43 = 0;
x_44 = l_Array_forIn_x27Unsafe_loop___redArg(x_7, x_39, x_28, x_42, x_43, x_41);
x_45 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_44, x_35);
return x_45;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, uint8_t x_21, uint8_t x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28) {
_start:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_box(x_2);
x_34 = lean_box(x_21);
x_35 = lean_box(x_22);
lean_inc(x_13);
lean_inc(x_5);
lean_inc(x_1);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed), 29, 28);
lean_closure_set(x_36, 0, x_1);
lean_closure_set(x_36, 1, x_33);
lean_closure_set(x_36, 2, x_3);
lean_closure_set(x_36, 3, x_4);
lean_closure_set(x_36, 4, x_5);
lean_closure_set(x_36, 5, x_6);
lean_closure_set(x_36, 6, x_7);
lean_closure_set(x_36, 7, x_8);
lean_closure_set(x_36, 8, x_9);
lean_closure_set(x_36, 9, x_10);
lean_closure_set(x_36, 10, x_30);
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
lean_closure_set(x_36, 21, x_34);
lean_closure_set(x_36, 22, x_35);
lean_closure_set(x_36, 23, x_23);
lean_closure_set(x_36, 24, x_24);
lean_closure_set(x_36, 25, x_25);
lean_closure_set(x_36, 26, x_32);
lean_closure_set(x_36, 27, x_26);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_31);
x_37 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = lean_apply_2(x_1, lean_box(0), x_27);
x_39 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_38, x_37);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_13, 0);
lean_inc(x_40);
lean_dec(x_13);
x_41 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(x_41, 0, x_36);
x_42 = lean_array_set(x_27, x_40, x_31);
lean_dec(x_40);
x_43 = lean_apply_2(x_1, lean_box(0), x_42);
x_44 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_43, x_41);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, uint8_t x_23, uint8_t x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30) {
_start:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_30);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed), 12, 10);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_2);
lean_closure_set(x_31, 2, x_3);
lean_closure_set(x_31, 3, x_30);
lean_closure_set(x_31, 4, x_4);
lean_closure_set(x_31, 5, x_5);
lean_closure_set(x_31, 6, x_6);
lean_closure_set(x_31, 7, x_7);
lean_closure_set(x_31, 8, x_8);
lean_closure_set(x_31, 9, x_9);
x_32 = lean_box(0);
x_33 = lean_box(x_23);
x_34 = lean_box(x_24);
lean_inc(x_5);
lean_inc(x_11);
lean_inc(x_3);
x_35 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed), 28, 27);
lean_closure_set(x_35, 0, x_1);
lean_closure_set(x_35, 1, x_32);
lean_closure_set(x_35, 2, x_2);
lean_closure_set(x_35, 3, x_10);
lean_closure_set(x_35, 4, x_3);
lean_closure_set(x_35, 5, x_11);
lean_closure_set(x_35, 6, x_5);
lean_closure_set(x_35, 7, x_12);
lean_closure_set(x_35, 8, x_13);
lean_closure_set(x_35, 9, x_14);
lean_closure_set(x_35, 10, x_30);
lean_closure_set(x_35, 11, x_15);
lean_closure_set(x_35, 12, x_16);
lean_closure_set(x_35, 13, x_4);
lean_closure_set(x_35, 14, x_17);
lean_closure_set(x_35, 15, x_18);
lean_closure_set(x_35, 16, x_19);
lean_closure_set(x_35, 17, x_20);
lean_closure_set(x_35, 18, x_21);
lean_closure_set(x_35, 19, x_22);
lean_closure_set(x_35, 20, x_33);
lean_closure_set(x_35, 21, x_34);
lean_closure_set(x_35, 22, x_9);
lean_closure_set(x_35, 23, x_25);
lean_closure_set(x_35, 24, x_26);
lean_closure_set(x_35, 25, x_27);
lean_closure_set(x_35, 26, x_28);
x_36 = lean_unbox(x_32);
x_37 = l_Lean_Meta_lambdaTelescope___redArg(x_11, x_5, x_29, x_31, x_36);
x_38 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_37, x_35);
return x_38;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, uint8_t x_22, uint8_t x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30) {
_start:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_box(x_22);
x_32 = lean_box(x_23);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_3);
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__62___boxed), 30, 29);
lean_closure_set(x_33, 0, x_1);
lean_closure_set(x_33, 1, x_2);
lean_closure_set(x_33, 2, x_3);
lean_closure_set(x_33, 3, x_4);
lean_closure_set(x_33, 4, x_5);
lean_closure_set(x_33, 5, x_6);
lean_closure_set(x_33, 6, x_7);
lean_closure_set(x_33, 7, x_8);
lean_closure_set(x_33, 8, x_9);
lean_closure_set(x_33, 9, x_10);
lean_closure_set(x_33, 10, x_11);
lean_closure_set(x_33, 11, x_12);
lean_closure_set(x_33, 12, x_13);
lean_closure_set(x_33, 13, x_30);
lean_closure_set(x_33, 14, x_14);
lean_closure_set(x_33, 15, x_15);
lean_closure_set(x_33, 16, x_16);
lean_closure_set(x_33, 17, x_17);
lean_closure_set(x_33, 18, x_18);
lean_closure_set(x_33, 19, x_19);
lean_closure_set(x_33, 20, x_20);
lean_closure_set(x_33, 21, x_21);
lean_closure_set(x_33, 22, x_31);
lean_closure_set(x_33, 23, x_32);
lean_closure_set(x_33, 24, x_24);
lean_closure_set(x_33, 25, x_25);
lean_closure_set(x_33, 26, x_26);
lean_closure_set(x_33, 27, x_27);
lean_closure_set(x_33, 28, x_28);
x_34 = lean_array_size(x_8);
x_35 = 0;
x_36 = l_Array_mapMUnsafe_map___redArg(x_5, x_29, x_34, x_35, x_8);
x_37 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_36, x_33);
return x_37;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__66(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, uint8_t x_22, uint8_t x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30) {
_start:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_box(x_22);
x_32 = lean_box(x_23);
lean_inc(x_28);
lean_inc(x_5);
lean_inc(x_3);
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__65___boxed), 30, 29);
lean_closure_set(x_33, 0, x_1);
lean_closure_set(x_33, 1, x_2);
lean_closure_set(x_33, 2, x_3);
lean_closure_set(x_33, 3, x_4);
lean_closure_set(x_33, 4, x_5);
lean_closure_set(x_33, 5, x_6);
lean_closure_set(x_33, 6, x_7);
lean_closure_set(x_33, 7, x_8);
lean_closure_set(x_33, 8, x_9);
lean_closure_set(x_33, 9, x_10);
lean_closure_set(x_33, 10, x_11);
lean_closure_set(x_33, 11, x_12);
lean_closure_set(x_33, 12, x_13);
lean_closure_set(x_33, 13, x_14);
lean_closure_set(x_33, 14, x_15);
lean_closure_set(x_33, 15, x_16);
lean_closure_set(x_33, 16, x_17);
lean_closure_set(x_33, 17, x_18);
lean_closure_set(x_33, 18, x_19);
lean_closure_set(x_33, 19, x_20);
lean_closure_set(x_33, 20, x_21);
lean_closure_set(x_33, 21, x_31);
lean_closure_set(x_33, 22, x_32);
lean_closure_set(x_33, 23, x_24);
lean_closure_set(x_33, 24, x_30);
lean_closure_set(x_33, 25, x_25);
lean_closure_set(x_33, 26, x_26);
lean_closure_set(x_33, 27, x_27);
lean_closure_set(x_33, 28, x_28);
x_34 = lean_array_size(x_29);
x_35 = 0;
x_36 = l_Array_mapMUnsafe_map___redArg(x_5, x_28, x_34, x_35, x_29);
x_37 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_36, x_33);
return x_37;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__67(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("matcher ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" has no MatchInfo found", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__69(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__1;
x_10 = l_Lean_MessageData_ofName(x_1);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__3;
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_ctor_get(x_8, 0);
x_17 = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(x_16);
x_18 = lean_apply_2(x_6, lean_box(0), x_17);
x_19 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_18, x_7);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__70(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, uint8_t x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 4);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 5);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 6);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 7);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 8);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 9);
lean_inc(x_31);
lean_dec(x_1);
lean_inc(x_22);
x_32 = l_Lean_isCasesOnRecursor(x_21, x_22);
x_33 = lean_box(x_16);
x_34 = lean_box(x_32);
lean_inc(x_22);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_35 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__66___boxed), 30, 29);
lean_closure_set(x_35, 0, x_2);
lean_closure_set(x_35, 1, x_3);
lean_closure_set(x_35, 2, x_4);
lean_closure_set(x_35, 3, x_25);
lean_closure_set(x_35, 4, x_5);
lean_closure_set(x_35, 5, x_6);
lean_closure_set(x_35, 6, x_7);
lean_closure_set(x_35, 7, x_28);
lean_closure_set(x_35, 8, x_8);
lean_closure_set(x_35, 9, x_9);
lean_closure_set(x_35, 10, x_10);
lean_closure_set(x_35, 11, x_11);
lean_closure_set(x_35, 12, x_22);
lean_closure_set(x_35, 13, x_29);
lean_closure_set(x_35, 14, x_24);
lean_closure_set(x_35, 15, x_12);
lean_closure_set(x_35, 16, x_31);
lean_closure_set(x_35, 17, x_30);
lean_closure_set(x_35, 18, x_13);
lean_closure_set(x_35, 19, x_14);
lean_closure_set(x_35, 20, x_15);
lean_closure_set(x_35, 21, x_33);
lean_closure_set(x_35, 22, x_34);
lean_closure_set(x_35, 23, x_17);
lean_closure_set(x_35, 24, x_18);
lean_closure_set(x_35, 25, x_23);
lean_closure_set(x_35, 26, x_27);
lean_closure_set(x_35, 27, x_19);
lean_closure_set(x_35, 28, x_26);
if (x_32 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__67), 2, 1);
lean_closure_set(x_36, 0, x_35);
lean_inc(x_36);
lean_inc(x_4);
lean_inc(x_5);
lean_inc(x_22);
x_37 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__69___boxed), 8, 7);
lean_closure_set(x_37, 0, x_22);
lean_closure_set(x_37, 1, x_5);
lean_closure_set(x_37, 2, x_8);
lean_closure_set(x_37, 3, x_4);
lean_closure_set(x_37, 4, x_36);
lean_closure_set(x_37, 5, x_2);
lean_closure_set(x_37, 6, x_36);
x_38 = l_Lean_Meta_getMatcherInfo_x3f___redArg(x_5, x_20, x_22);
x_39 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_38, x_37);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_5);
x_40 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__67), 2, 1);
lean_closure_set(x_40, 0, x_35);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_apply_2(x_2, lean_box(0), x_41);
x_43 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_42, x_40);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
lean_inc(x_4);
lean_inc(x_3);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_20, 0, x_3);
lean_closure_set(x_20, 1, x_4);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_21, 0, x_1);
lean_inc(x_3);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed), 4, 2);
lean_closure_set(x_22, 0, x_3);
lean_closure_set(x_22, 1, x_21);
lean_inc(x_1);
lean_inc(x_17);
lean_inc(x_19);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7), 6, 3);
lean_closure_set(x_23, 0, x_19);
lean_closure_set(x_23, 1, x_17);
lean_closure_set(x_23, 2, x_1);
x_24 = lean_box(x_11);
lean_inc(x_1);
lean_inc(x_17);
lean_inc(x_19);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__13___boxed), 7, 4);
lean_closure_set(x_25, 0, x_19);
lean_closure_set(x_25, 1, x_17);
lean_closure_set(x_25, 2, x_24);
lean_closure_set(x_25, 3, x_1);
x_26 = lean_box(x_10);
lean_inc(x_17);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__70___boxed), 21, 20);
lean_closure_set(x_27, 0, x_9);
lean_closure_set(x_27, 1, x_19);
lean_closure_set(x_27, 2, x_1);
lean_closure_set(x_27, 3, x_17);
lean_closure_set(x_27, 4, x_3);
lean_closure_set(x_27, 5, x_25);
lean_closure_set(x_27, 6, x_13);
lean_closure_set(x_27, 7, x_4);
lean_closure_set(x_27, 8, x_14);
lean_closure_set(x_27, 9, x_2);
lean_closure_set(x_27, 10, x_22);
lean_closure_set(x_27, 11, x_15);
lean_closure_set(x_27, 12, x_6);
lean_closure_set(x_27, 13, x_7);
lean_closure_set(x_27, 14, x_8);
lean_closure_set(x_27, 15, x_26);
lean_closure_set(x_27, 16, x_20);
lean_closure_set(x_27, 17, x_23);
lean_closure_set(x_27, 18, x_12);
lean_closure_set(x_27, 19, x_5);
x_28 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_18, x_27);
return x_28;
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_MatcherApp_transform___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_MatcherApp_transform___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_MatcherApp_transform___redArg___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_MatcherApp_transform___redArg___lam__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_MatcherApp_transform___redArg___lam__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_transform___redArg___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__6(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_MatcherApp_transform___redArg___lam__8(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_transform___redArg___lam__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_MatcherApp_transform___redArg___lam__10(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_transform___redArg___lam__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_11);
lean_dec(x_11);
x_13 = l_Lean_Meta_MatcherApp_transform___redArg___lam__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__13(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_MatcherApp_transform___redArg___lam__19(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_MatcherApp_transform___redArg___lam__22(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_MatcherApp_transform___redArg___lam__21(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__23(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Meta_MatcherApp_transform___redArg___lam__26(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = l_Lean_Meta_MatcherApp_transform___redArg___lam__27(x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_MatcherApp_transform___redArg___lam__28(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Meta_MatcherApp_transform___redArg___lam__30(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_MatcherApp_transform___redArg___lam__31(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
return x_14;
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
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
_start:
{
lean_object* x_23; 
x_23 = l_Lean_Meta_MatcherApp_transform___redArg___lam__34(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_MatcherApp_transform___redArg___lam__36(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_10);
lean_dec(x_10);
x_12 = l_Lean_Meta_MatcherApp_transform___redArg___lam__38(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_Meta_MatcherApp_transform___redArg___lam__37(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Lean_Meta_MatcherApp_transform___redArg___lam__40(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed(lean_object** _args) {
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
lean_dec(x_4);
x_19 = lean_unbox(x_5);
lean_dec(x_5);
x_20 = l_Lean_Meta_MatcherApp_transform___redArg___lam__41(x_1, x_2, x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42___boxed(lean_object** _args) {
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
lean_dec(x_3);
x_19 = lean_unbox(x_4);
lean_dec(x_4);
x_20 = l_Lean_Meta_MatcherApp_transform___redArg___lam__42(x_1, x_2, x_18, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__43(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed(lean_object** _args) {
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
lean_dec(x_2);
x_19 = lean_unbox(x_3);
lean_dec(x_3);
x_20 = l_Lean_Meta_MatcherApp_transform___redArg___lam__44(x_1, x_18, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__45(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = lean_unbox(x_4);
lean_dec(x_4);
x_19 = l_Lean_Meta_MatcherApp_transform___redArg___lam__47(x_1, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_MatcherApp_transform___redArg___lam__49(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
return x_14;
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
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
_start:
{
lean_object* x_26; 
x_26 = l_Lean_Meta_MatcherApp_transform___redArg___lam__51(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
lean_dec(x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Lean_Meta_MatcherApp_transform___redArg___lam__55(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56___boxed(lean_object** _args) {
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
lean_object* x_25; 
x_25 = l_Lean_Meta_MatcherApp_transform___redArg___lam__56(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object** _args) {
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
lean_object* x_25; 
x_25 = l_Lean_Meta_MatcherApp_transform___redArg___lam__57(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
return x_25;
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
_start:
{
lean_object* x_25; 
x_25 = l_Lean_Meta_MatcherApp_transform___redArg___lam__58(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
lean_dec(x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Lean_Meta_MatcherApp_transform___redArg___lam__63(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
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
_start:
{
uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_unbox(x_2);
lean_dec(x_2);
x_32 = lean_unbox(x_25);
lean_dec(x_25);
x_33 = lean_unbox(x_26);
lean_dec(x_26);
x_34 = l_Lean_Meta_MatcherApp_transform___redArg___lam__59(x_1, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_32, x_33, x_27, x_28, x_29, x_30);
return x_34;
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
_start:
{
uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; 
x_30 = lean_unbox(x_2);
lean_dec(x_2);
x_31 = lean_unbox(x_22);
lean_dec(x_22);
x_32 = lean_unbox(x_23);
lean_dec(x_23);
x_33 = l_Lean_Meta_MatcherApp_transform___redArg___lam__60(x_1, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_31, x_32, x_24, x_25, x_26, x_27, x_28, x_29);
return x_33;
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
_start:
{
uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; 
x_29 = lean_unbox(x_2);
lean_dec(x_2);
x_30 = lean_unbox(x_21);
lean_dec(x_21);
x_31 = lean_unbox(x_22);
lean_dec(x_22);
x_32 = l_Lean_Meta_MatcherApp_transform___redArg___lam__64(x_1, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_30, x_31, x_23, x_24, x_25, x_26, x_27, x_28);
return x_32;
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
_start:
{
uint8_t x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_unbox(x_23);
lean_dec(x_23);
x_32 = lean_unbox(x_24);
lean_dec(x_24);
x_33 = l_Lean_Meta_MatcherApp_transform___redArg___lam__62(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_31, x_32, x_25, x_26, x_27, x_28, x_29, x_30);
return x_33;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65___boxed(lean_object** _args) {
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
uint8_t x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_unbox(x_22);
lean_dec(x_22);
x_32 = lean_unbox(x_23);
lean_dec(x_23);
x_33 = l_Lean_Meta_MatcherApp_transform___redArg___lam__65(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_31, x_32, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
return x_33;
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
_start:
{
uint8_t x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_unbox(x_22);
lean_dec(x_22);
x_32 = lean_unbox(x_23);
lean_dec(x_23);
x_33 = l_Lean_Meta_MatcherApp_transform___redArg___lam__66(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_31, x_32, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
return x_33;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__69___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_MatcherApp_transform___redArg___lam__69(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__70___boxed(lean_object** _args) {
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
uint8_t x_22; lean_object* x_23; 
x_22 = lean_unbox(x_16);
lean_dec(x_16);
x_23 = l_Lean_Meta_MatcherApp_transform___redArg___lam__70(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_22, x_17, x_18, x_19, x_20, x_21);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_10);
lean_dec(x_10);
x_17 = lean_unbox(x_11);
lean_dec(x_11);
x_18 = l_Lean_Meta_MatcherApp_transform___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16, x_17, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_11);
lean_dec(x_11);
x_18 = lean_unbox(x_12);
lean_dec(x_12);
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
lean_object* x_30; uint8_t x_31; 
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
return x_31;
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
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Type ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" of alternative ", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" still depends on ", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_6, x_5);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_7);
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_array_uget(x_21, x_6);
x_23 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0(x_22, x_1);
if (x_23 == 0)
{
lean_dec(x_22);
lean_inc(x_2);
x_13 = x_2;
x_14 = x_12;
goto block_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_24 = l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__1;
x_25 = l_Lean_MessageData_ofExpr(x_1);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__3;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_MessageData_ofExpr(x_3);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__5;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_MessageData_ofExpr(x_22);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__3;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_36, x_8, x_9, x_10, x_11, x_12);
return x_37;
}
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_6, x_15);
x_6 = x_16;
x_7 = x_13;
x_12 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_6, x_5);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_7);
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_array_uget(x_21, x_6);
x_23 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0(x_22, x_1);
if (x_23 == 0)
{
lean_dec(x_22);
lean_inc(x_2);
x_13 = x_2;
x_14 = x_12;
goto block_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_24 = l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__1;
x_25 = l_Lean_MessageData_ofExpr(x_1);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__3;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_MessageData_ofExpr(x_3);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__5;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_MessageData_ofExpr(x_22);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__3;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_36, x_8, x_9, x_10, x_11, x_12);
return x_37;
}
}
block_18:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 1;
x_16 = lean_usize_add(x_6, x_15);
x_17 = l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_16, x_13, x_8, x_9, x_10, x_11, x_14);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = lean_infer_type(x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_6);
x_17 = lean_nat_sub(x_16, x_1);
lean_inc(x_17);
lean_inc(x_6);
x_18 = l_Array_toSubarray___redArg(x_6, x_17, x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
x_21 = lean_box(0);
x_22 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
lean_inc(x_14);
x_24 = l_Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1(x_14, x_21, x_2, x_18, x_22, x_23, x_21, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Array_toSubarray___redArg(x_6, x_26, x_17);
x_28 = l_Array_ofSubarray___redArg(x_27);
lean_dec(x_27);
x_29 = l_Lean_Meta_mkLambdaFVars(x_28, x_14, x_3, x_4, x_3, x_5, x_8, x_9, x_10, x_11, x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_array_uget(x_7, x_6);
x_16 = lean_box(x_2);
x_17 = lean_box(x_3);
x_18 = lean_box(x_4);
lean_inc(x_15);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___lam__0___boxed), 12, 5);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_15);
lean_closure_set(x_19, 2, x_16);
lean_closure_set(x_19, 3, x_17);
lean_closure_set(x_19, 4, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_20 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_15, x_19, x_2, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = lean_array_uset(x_7, x_6, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_6, x_25);
x_27 = lean_array_uset(x_24, x_6, x_21);
x_6 = x_26;
x_7 = x_27;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_array_uget(x_7, x_6);
x_16 = lean_box(x_2);
x_17 = lean_box(x_3);
x_18 = lean_box(x_4);
lean_inc(x_15);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___lam__0___boxed), 12, 5);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_15);
lean_closure_set(x_19, 2, x_16);
lean_closure_set(x_19, 3, x_17);
lean_closure_set(x_19, 4, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_20 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_15, x_19, x_2, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = lean_array_uset(x_7, x_6, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_6, x_25);
x_27 = lean_array_uset(x_24, x_6, x_21);
x_28 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_26, x_27, x_8, x_9, x_10, x_11, x_22);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
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
lean_dec(x_4);
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
lean_inc(x_4);
x_12 = l_Lean_FVarId_getUserName___redArg(x_11, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
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
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = lean_apply_6(x_1, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_inc(x_28);
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
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_inc(x_40);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_23, 2);
lean_inc(x_42);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_29, x_43);
lean_inc(x_28);
lean_ctor_set(x_21, 1, x_44);
x_45 = lean_nat_dec_lt(x_41, x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_inc(x_40);
lean_ctor_set(x_23, 1, x_54);
if (x_1 == 0)
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_28);
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_array_fget(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_22);
x_62 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_62);
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
lean_dec(x_63);
x_67 = lean_array_fget(x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_68 = l_Lean_Meta_mkEqHEq(x_67, x_62, x_6, x_7, x_8, x_9, x_66);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
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
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_62);
lean_dec(x_41);
lean_dec(x_40);
x_94 = lean_ctor_get(x_63, 1);
lean_inc(x_94);
lean_dec(x_63);
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
lean_dec(x_62);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_40);
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
lean_inc(x_40);
x_105 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_105, 0, x_40);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_105, 2, x_42);
if (x_1 == 0)
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_28);
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_array_fget(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_22);
x_113 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_113);
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
lean_dec(x_114);
x_118 = lean_array_fget(x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_119 = l_Lean_Meta_mkEqHEq(x_118, x_113, x_6, x_7, x_8, x_9, x_117);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
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
lean_dec(x_105);
lean_dec(x_21);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_113);
lean_dec(x_41);
lean_dec(x_40);
x_137 = lean_ctor_get(x_114, 1);
lean_inc(x_137);
lean_dec(x_114);
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
lean_dec(x_113);
lean_dec(x_105);
lean_dec(x_21);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_40);
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
lean_inc(x_147);
x_148 = lean_ctor_get(x_23, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_23, 2);
lean_inc(x_149);
x_150 = lean_unsigned_to_nat(1u);
x_151 = lean_nat_add(x_29, x_150);
lean_inc(x_28);
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
lean_dec(x_147);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_inc(x_147);
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
lean_dec(x_147);
lean_dec(x_29);
lean_dec(x_28);
goto block_166;
}
else
{
lean_object* x_167; 
x_167 = lean_array_fget(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_22);
x_168 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_168);
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
lean_dec(x_169);
x_173 = lean_array_fget(x_147, x_148);
lean_dec(x_148);
lean_dec(x_147);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_174 = l_Lean_Meta_mkEqHEq(x_173, x_168, x_6, x_7, x_8, x_9, x_172);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
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
lean_dec(x_160);
lean_dec(x_152);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_168);
lean_dec(x_148);
lean_dec(x_147);
x_192 = lean_ctor_get(x_169, 1);
lean_inc(x_192);
lean_dec(x_169);
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
lean_dec(x_168);
lean_dec(x_160);
lean_dec(x_152);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_147);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_inc(x_24);
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
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* x_52; lean_object* x_53; uint8_t x_56; 
x_52 = lean_ctor_get(x_35, 0);
lean_inc(x_52);
lean_dec(x_35);
x_53 = lean_array_uget(x_1, x_3);
x_56 = lean_unbox(x_52);
lean_dec(x_52);
if (x_56 == 0)
{
goto block_55;
}
else
{
if (x_27 == 0)
{
goto block_55;
}
else
{
lean_object* x_57; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_57 = l_Lean_Meta_mkHEqRefl(x_53, x_5, x_6, x_7, x_8, x_9);
x_38 = x_57;
goto block_49;
}
}
block_55:
{
lean_object* x_54; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_54 = l_Lean_Meta_mkEqRefl(x_53, x_5, x_6, x_7, x_8, x_9);
x_38 = x_54;
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
lean_dec(x_38);
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
lean_dec(x_19);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_19);
x_58 = lean_array_fget(x_24, x_25);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_25, x_59);
lean_dec(x_25);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_24);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_26);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_23);
lean_dec(x_20);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_21);
lean_ctor_set(x_74, 1, x_22);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_61);
lean_ctor_set(x_75, 1, x_74);
x_10 = x_75;
x_11 = x_9;
goto block_15;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_80; 
x_76 = lean_ctor_get(x_58, 0);
lean_inc(x_76);
lean_dec(x_58);
x_77 = lean_array_uget(x_1, x_3);
x_80 = lean_unbox(x_76);
lean_dec(x_76);
if (x_80 == 0)
{
goto block_79;
}
else
{
if (x_27 == 0)
{
goto block_79;
}
else
{
lean_object* x_81; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_81 = l_Lean_Meta_mkHEqRefl(x_77, x_5, x_6, x_7, x_8, x_9);
x_62 = x_81;
goto block_73;
}
}
block_79:
{
lean_object* x_78; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_78 = l_Lean_Meta_mkEqRefl(x_77, x_5, x_6, x_7, x_8, x_9);
x_62 = x_78;
goto block_73;
}
}
block_73:
{
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_array_push(x_22, x_63);
x_66 = lean_nat_add(x_21, x_59);
lean_dec(x_21);
if (lean_is_scalar(x_23)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_23;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
if (lean_is_scalar(x_20)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_20;
}
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_67);
x_10 = x_68;
x_11 = x_64;
goto block_15;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_61);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_69 = lean_ctor_get(x_62, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_71 = x_62;
} else {
 lean_dec_ref(x_62);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_7(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg___lam__0___boxed), 10, 1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_14 = l_Lean_Meta_instantiateLambda(x_1, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_17 = lean_apply_8(x_3, x_4, x_5, x_15, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Array_append___redArg(x_2, x_6);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_Meta_mkLambdaFVars(x_20, x_18, x_7, x_8, x_7, x_22, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_23;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
return x_17;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_15 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(x_3);
x_19 = lean_box(x_7);
lean_inc(x_4);
x_20 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__0___boxed), 13, 8);
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
lean_dec(x_4);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_box(x_3);
x_16 = lean_box(x_6);
x_17 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__1___boxed), 14, 7);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_15);
lean_closure_set(x_17, 3, x_8);
lean_closure_set(x_17, 4, x_4);
lean_closure_set(x_17, 5, x_5);
lean_closure_set(x_17, 6, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_7);
x_19 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_9, x_18, x_17, x_3, x_10, x_11, x_12, x_13, x_14);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_nat_dec_lt(x_8, x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_19, 1);
x_29 = lean_ctor_get(x_19, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_20, 2);
lean_inc(x_32);
x_33 = lean_nat_dec_lt(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_13);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_36 = lean_ctor_get(x_20, 2);
lean_dec(x_36);
x_37 = lean_ctor_get(x_20, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_20, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_25, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_25, 2);
lean_inc(x_41);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_31, x_42);
lean_inc(x_30);
lean_ctor_set(x_20, 1, x_43);
x_44 = lean_nat_dec_lt(x_40, x_41);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_7);
lean_ctor_set(x_45, 1, x_13);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_25);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_47 = lean_ctor_get(x_25, 2);
lean_dec(x_47);
x_48 = lean_ctor_get(x_25, 1);
lean_dec(x_48);
x_49 = lean_ctor_get(x_25, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_22, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_22, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_22, 2);
lean_inc(x_52);
x_53 = lean_nat_add(x_40, x_42);
lean_inc(x_39);
lean_ctor_set(x_25, 1, x_53);
x_54 = lean_nat_dec_lt(x_51, x_52);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_7);
lean_ctor_set(x_55, 1, x_13);
return x_55;
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_22);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_57 = lean_ctor_get(x_22, 2);
lean_dec(x_57);
x_58 = lean_ctor_get(x_22, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_22, 0);
lean_dec(x_59);
x_60 = lean_array_fget(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
x_61 = lean_array_fget(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
x_62 = lean_array_fget(x_50, x_51);
x_63 = lean_box(x_2);
x_64 = lean_box(x_4);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_65 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2___boxed), 14, 7);
lean_closure_set(x_65, 0, x_62);
lean_closure_set(x_65, 1, x_1);
lean_closure_set(x_65, 2, x_63);
lean_closure_set(x_65, 3, x_3);
lean_closure_set(x_65, 4, x_8);
lean_closure_set(x_65, 5, x_64);
lean_closure_set(x_65, 6, x_5);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_67 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_60, x_66, x_65, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_nat_add(x_51, x_42);
lean_dec(x_51);
lean_ctor_set(x_22, 1, x_70);
x_71 = lean_array_push(x_28, x_68);
lean_ctor_set(x_19, 1, x_71);
x_72 = lean_nat_add(x_8, x_15);
lean_dec(x_8);
x_8 = x_72;
x_13 = x_69;
goto _start;
}
else
{
uint8_t x_74; 
lean_free_object(x_22);
lean_dec(x_25);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_20);
lean_free_object(x_19);
lean_dec(x_28);
lean_free_object(x_18);
lean_free_object(x_7);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_67);
if (x_74 == 0)
{
return x_67;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_67, 0);
x_76 = lean_ctor_get(x_67, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_67);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_22);
x_78 = lean_array_fget(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
x_79 = lean_array_fget(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
x_80 = lean_array_fget(x_50, x_51);
x_81 = lean_box(x_2);
x_82 = lean_box(x_4);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_83 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2___boxed), 14, 7);
lean_closure_set(x_83, 0, x_80);
lean_closure_set(x_83, 1, x_1);
lean_closure_set(x_83, 2, x_81);
lean_closure_set(x_83, 3, x_3);
lean_closure_set(x_83, 4, x_8);
lean_closure_set(x_83, 5, x_82);
lean_closure_set(x_83, 6, x_5);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_79);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_85 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_78, x_84, x_83, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_nat_add(x_51, x_42);
lean_dec(x_51);
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_50);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 2, x_52);
x_90 = lean_array_push(x_28, x_86);
lean_ctor_set(x_19, 1, x_90);
lean_ctor_set(x_7, 0, x_89);
x_91 = lean_nat_add(x_8, x_15);
lean_dec(x_8);
x_8 = x_91;
x_13 = x_87;
goto _start;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_25);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_20);
lean_free_object(x_19);
lean_dec(x_28);
lean_free_object(x_18);
lean_free_object(x_7);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_93 = lean_ctor_get(x_85, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_85, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_95 = x_85;
} else {
 lean_dec_ref(x_85);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_25);
x_97 = lean_ctor_get(x_22, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_22, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_22, 2);
lean_inc(x_99);
x_100 = lean_nat_add(x_40, x_42);
lean_inc(x_39);
x_101 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_101, 0, x_39);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_101, 2, x_41);
x_102 = lean_nat_dec_lt(x_98, x_99);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_18, 0, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_7);
lean_ctor_set(x_103, 1, x_13);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 x_104 = x_22;
} else {
 lean_dec_ref(x_22);
 x_104 = lean_box(0);
}
x_105 = lean_array_fget(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
x_106 = lean_array_fget(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
x_107 = lean_array_fget(x_97, x_98);
x_108 = lean_box(x_2);
x_109 = lean_box(x_4);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_110 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2___boxed), 14, 7);
lean_closure_set(x_110, 0, x_107);
lean_closure_set(x_110, 1, x_1);
lean_closure_set(x_110, 2, x_108);
lean_closure_set(x_110, 3, x_3);
lean_closure_set(x_110, 4, x_8);
lean_closure_set(x_110, 5, x_109);
lean_closure_set(x_110, 6, x_5);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_106);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_112 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_105, x_111, x_110, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_nat_add(x_98, x_42);
lean_dec(x_98);
if (lean_is_scalar(x_104)) {
 x_116 = lean_alloc_ctor(0, 3, 0);
} else {
 x_116 = x_104;
}
lean_ctor_set(x_116, 0, x_97);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_116, 2, x_99);
x_117 = lean_array_push(x_28, x_113);
lean_ctor_set(x_19, 1, x_117);
lean_ctor_set(x_18, 0, x_101);
lean_ctor_set(x_7, 0, x_116);
x_118 = lean_nat_add(x_8, x_15);
lean_dec(x_8);
x_8 = x_118;
x_13 = x_114;
goto _start;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_104);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_20);
lean_free_object(x_19);
lean_dec(x_28);
lean_free_object(x_18);
lean_free_object(x_7);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_120 = lean_ctor_get(x_112, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_112, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_122 = x_112;
} else {
 lean_dec_ref(x_112);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
lean_dec(x_20);
x_124 = lean_ctor_get(x_25, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_25, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_25, 2);
lean_inc(x_126);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_nat_add(x_31, x_127);
lean_inc(x_30);
x_129 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_129, 0, x_30);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_32);
x_130 = lean_nat_dec_lt(x_125, x_126);
if (x_130 == 0)
{
lean_object* x_131; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_19, 0, x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_7);
lean_ctor_set(x_131, 1, x_13);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_132 = x_25;
} else {
 lean_dec_ref(x_25);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_22, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_22, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_22, 2);
lean_inc(x_135);
x_136 = lean_nat_add(x_125, x_127);
lean_inc(x_124);
if (lean_is_scalar(x_132)) {
 x_137 = lean_alloc_ctor(0, 3, 0);
} else {
 x_137 = x_132;
}
lean_ctor_set(x_137, 0, x_124);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set(x_137, 2, x_126);
x_138 = lean_nat_dec_lt(x_134, x_135);
if (x_138 == 0)
{
lean_object* x_139; 
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_19, 0, x_129);
lean_ctor_set(x_18, 0, x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_7);
lean_ctor_set(x_139, 1, x_13);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 x_140 = x_22;
} else {
 lean_dec_ref(x_22);
 x_140 = lean_box(0);
}
x_141 = lean_array_fget(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
x_142 = lean_array_fget(x_124, x_125);
lean_dec(x_125);
lean_dec(x_124);
x_143 = lean_array_fget(x_133, x_134);
x_144 = lean_box(x_2);
x_145 = lean_box(x_4);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_146 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2___boxed), 14, 7);
lean_closure_set(x_146, 0, x_143);
lean_closure_set(x_146, 1, x_1);
lean_closure_set(x_146, 2, x_144);
lean_closure_set(x_146, 3, x_3);
lean_closure_set(x_146, 4, x_8);
lean_closure_set(x_146, 5, x_145);
lean_closure_set(x_146, 6, x_5);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_142);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_148 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_141, x_147, x_146, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_nat_add(x_134, x_127);
lean_dec(x_134);
if (lean_is_scalar(x_140)) {
 x_152 = lean_alloc_ctor(0, 3, 0);
} else {
 x_152 = x_140;
}
lean_ctor_set(x_152, 0, x_133);
lean_ctor_set(x_152, 1, x_151);
lean_ctor_set(x_152, 2, x_135);
x_153 = lean_array_push(x_28, x_149);
lean_ctor_set(x_19, 1, x_153);
lean_ctor_set(x_19, 0, x_129);
lean_ctor_set(x_18, 0, x_137);
lean_ctor_set(x_7, 0, x_152);
x_154 = lean_nat_add(x_8, x_15);
lean_dec(x_8);
x_8 = x_154;
x_13 = x_150;
goto _start;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_140);
lean_dec(x_137);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_129);
lean_free_object(x_19);
lean_dec(x_28);
lean_free_object(x_18);
lean_free_object(x_7);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_156 = lean_ctor_get(x_148, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_148, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_158 = x_148;
} else {
 lean_dec_ref(x_148);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
}
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_160 = lean_ctor_get(x_19, 1);
lean_inc(x_160);
lean_dec(x_19);
x_161 = lean_ctor_get(x_20, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_20, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_20, 2);
lean_inc(x_163);
x_164 = lean_nat_dec_lt(x_162, x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_20);
lean_ctor_set(x_165, 1, x_160);
lean_ctor_set(x_18, 1, x_165);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_7);
lean_ctor_set(x_166, 1, x_13);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 x_167 = x_20;
} else {
 lean_dec_ref(x_20);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_25, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_25, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_25, 2);
lean_inc(x_170);
x_171 = lean_unsigned_to_nat(1u);
x_172 = lean_nat_add(x_162, x_171);
lean_inc(x_161);
if (lean_is_scalar(x_167)) {
 x_173 = lean_alloc_ctor(0, 3, 0);
} else {
 x_173 = x_167;
}
lean_ctor_set(x_173, 0, x_161);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set(x_173, 2, x_163);
x_174 = lean_nat_dec_lt(x_169, x_170);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_160);
lean_ctor_set(x_18, 1, x_175);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_7);
lean_ctor_set(x_176, 1, x_13);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_177 = x_25;
} else {
 lean_dec_ref(x_25);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_22, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_22, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_22, 2);
lean_inc(x_180);
x_181 = lean_nat_add(x_169, x_171);
lean_inc(x_168);
if (lean_is_scalar(x_177)) {
 x_182 = lean_alloc_ctor(0, 3, 0);
} else {
 x_182 = x_177;
}
lean_ctor_set(x_182, 0, x_168);
lean_ctor_set(x_182, 1, x_181);
lean_ctor_set(x_182, 2, x_170);
x_183 = lean_nat_dec_lt(x_179, x_180);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_173);
lean_ctor_set(x_184, 1, x_160);
lean_ctor_set(x_18, 1, x_184);
lean_ctor_set(x_18, 0, x_182);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_7);
lean_ctor_set(x_185, 1, x_13);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 x_186 = x_22;
} else {
 lean_dec_ref(x_22);
 x_186 = lean_box(0);
}
x_187 = lean_array_fget(x_161, x_162);
lean_dec(x_162);
lean_dec(x_161);
x_188 = lean_array_fget(x_168, x_169);
lean_dec(x_169);
lean_dec(x_168);
x_189 = lean_array_fget(x_178, x_179);
x_190 = lean_box(x_2);
x_191 = lean_box(x_4);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_192 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2___boxed), 14, 7);
lean_closure_set(x_192, 0, x_189);
lean_closure_set(x_192, 1, x_1);
lean_closure_set(x_192, 2, x_190);
lean_closure_set(x_192, 3, x_3);
lean_closure_set(x_192, 4, x_8);
lean_closure_set(x_192, 5, x_191);
lean_closure_set(x_192, 6, x_5);
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_188);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_194 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_187, x_193, x_192, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_nat_add(x_179, x_171);
lean_dec(x_179);
if (lean_is_scalar(x_186)) {
 x_198 = lean_alloc_ctor(0, 3, 0);
} else {
 x_198 = x_186;
}
lean_ctor_set(x_198, 0, x_178);
lean_ctor_set(x_198, 1, x_197);
lean_ctor_set(x_198, 2, x_180);
x_199 = lean_array_push(x_160, x_195);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_173);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set(x_18, 1, x_200);
lean_ctor_set(x_18, 0, x_182);
lean_ctor_set(x_7, 0, x_198);
x_201 = lean_nat_add(x_8, x_15);
lean_dec(x_8);
x_8 = x_201;
x_13 = x_196;
goto _start;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_186);
lean_dec(x_182);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_173);
lean_dec(x_160);
lean_free_object(x_18);
lean_free_object(x_7);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_203 = lean_ctor_get(x_194, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_194, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_205 = x_194;
} else {
 lean_dec_ref(x_194);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_204);
return x_206;
}
}
}
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_207 = lean_ctor_get(x_18, 0);
lean_inc(x_207);
lean_dec(x_18);
x_208 = lean_ctor_get(x_19, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_209 = x_19;
} else {
 lean_dec_ref(x_19);
 x_209 = lean_box(0);
}
x_210 = lean_ctor_get(x_20, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_20, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_20, 2);
lean_inc(x_212);
x_213 = lean_nat_dec_lt(x_211, x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_209)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_209;
}
lean_ctor_set(x_214, 0, x_20);
lean_ctor_set(x_214, 1, x_208);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_207);
lean_ctor_set(x_215, 1, x_214);
lean_ctor_set(x_7, 1, x_215);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_7);
lean_ctor_set(x_216, 1, x_13);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 x_217 = x_20;
} else {
 lean_dec_ref(x_20);
 x_217 = lean_box(0);
}
x_218 = lean_ctor_get(x_207, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_207, 1);
lean_inc(x_219);
x_220 = lean_ctor_get(x_207, 2);
lean_inc(x_220);
x_221 = lean_unsigned_to_nat(1u);
x_222 = lean_nat_add(x_211, x_221);
lean_inc(x_210);
if (lean_is_scalar(x_217)) {
 x_223 = lean_alloc_ctor(0, 3, 0);
} else {
 x_223 = x_217;
}
lean_ctor_set(x_223, 0, x_210);
lean_ctor_set(x_223, 1, x_222);
lean_ctor_set(x_223, 2, x_212);
x_224 = lean_nat_dec_lt(x_219, x_220);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_209)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_209;
}
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_208);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_207);
lean_ctor_set(x_226, 1, x_225);
lean_ctor_set(x_7, 1, x_226);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_7);
lean_ctor_set(x_227, 1, x_13);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 x_228 = x_207;
} else {
 lean_dec_ref(x_207);
 x_228 = lean_box(0);
}
x_229 = lean_ctor_get(x_22, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_22, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_22, 2);
lean_inc(x_231);
x_232 = lean_nat_add(x_219, x_221);
lean_inc(x_218);
if (lean_is_scalar(x_228)) {
 x_233 = lean_alloc_ctor(0, 3, 0);
} else {
 x_233 = x_228;
}
lean_ctor_set(x_233, 0, x_218);
lean_ctor_set(x_233, 1, x_232);
lean_ctor_set(x_233, 2, x_220);
x_234 = lean_nat_dec_lt(x_230, x_231);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_209)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_209;
}
lean_ctor_set(x_235, 0, x_223);
lean_ctor_set(x_235, 1, x_208);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_235);
lean_ctor_set(x_7, 1, x_236);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_7);
lean_ctor_set(x_237, 1, x_13);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 x_238 = x_22;
} else {
 lean_dec_ref(x_22);
 x_238 = lean_box(0);
}
x_239 = lean_array_fget(x_210, x_211);
lean_dec(x_211);
lean_dec(x_210);
x_240 = lean_array_fget(x_218, x_219);
lean_dec(x_219);
lean_dec(x_218);
x_241 = lean_array_fget(x_229, x_230);
x_242 = lean_box(x_2);
x_243 = lean_box(x_4);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_244 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2___boxed), 14, 7);
lean_closure_set(x_244, 0, x_241);
lean_closure_set(x_244, 1, x_1);
lean_closure_set(x_244, 2, x_242);
lean_closure_set(x_244, 3, x_3);
lean_closure_set(x_244, 4, x_8);
lean_closure_set(x_244, 5, x_243);
lean_closure_set(x_244, 6, x_5);
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_240);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_246 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_239, x_245, x_244, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = lean_nat_add(x_230, x_221);
lean_dec(x_230);
if (lean_is_scalar(x_238)) {
 x_250 = lean_alloc_ctor(0, 3, 0);
} else {
 x_250 = x_238;
}
lean_ctor_set(x_250, 0, x_229);
lean_ctor_set(x_250, 1, x_249);
lean_ctor_set(x_250, 2, x_231);
x_251 = lean_array_push(x_208, x_247);
if (lean_is_scalar(x_209)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_209;
}
lean_ctor_set(x_252, 0, x_223);
lean_ctor_set(x_252, 1, x_251);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_233);
lean_ctor_set(x_253, 1, x_252);
lean_ctor_set(x_7, 1, x_253);
lean_ctor_set(x_7, 0, x_250);
x_254 = lean_nat_add(x_8, x_15);
lean_dec(x_8);
x_8 = x_254;
x_13 = x_248;
goto _start;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_238);
lean_dec(x_233);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_223);
lean_dec(x_209);
lean_dec(x_208);
lean_free_object(x_7);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_256 = lean_ctor_get(x_246, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_246, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_258 = x_246;
} else {
 lean_dec_ref(x_246);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
}
}
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_260 = lean_ctor_get(x_7, 0);
lean_inc(x_260);
lean_dec(x_7);
x_261 = lean_ctor_get(x_18, 0);
lean_inc(x_261);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_262 = x_18;
} else {
 lean_dec_ref(x_18);
 x_262 = lean_box(0);
}
x_263 = lean_ctor_get(x_19, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_264 = x_19;
} else {
 lean_dec_ref(x_19);
 x_264 = lean_box(0);
}
x_265 = lean_ctor_get(x_20, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_20, 1);
lean_inc(x_266);
x_267 = lean_ctor_get(x_20, 2);
lean_inc(x_267);
x_268 = lean_nat_dec_lt(x_266, x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_264)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_264;
}
lean_ctor_set(x_269, 0, x_20);
lean_ctor_set(x_269, 1, x_263);
if (lean_is_scalar(x_262)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_262;
}
lean_ctor_set(x_270, 0, x_261);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_260);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_13);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 x_273 = x_20;
} else {
 lean_dec_ref(x_20);
 x_273 = lean_box(0);
}
x_274 = lean_ctor_get(x_261, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_261, 1);
lean_inc(x_275);
x_276 = lean_ctor_get(x_261, 2);
lean_inc(x_276);
x_277 = lean_unsigned_to_nat(1u);
x_278 = lean_nat_add(x_266, x_277);
lean_inc(x_265);
if (lean_is_scalar(x_273)) {
 x_279 = lean_alloc_ctor(0, 3, 0);
} else {
 x_279 = x_273;
}
lean_ctor_set(x_279, 0, x_265);
lean_ctor_set(x_279, 1, x_278);
lean_ctor_set(x_279, 2, x_267);
x_280 = lean_nat_dec_lt(x_275, x_276);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_264)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_264;
}
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_263);
if (lean_is_scalar(x_262)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_262;
}
lean_ctor_set(x_282, 0, x_261);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_260);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_13);
return x_284;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 x_285 = x_261;
} else {
 lean_dec_ref(x_261);
 x_285 = lean_box(0);
}
x_286 = lean_ctor_get(x_260, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_260, 1);
lean_inc(x_287);
x_288 = lean_ctor_get(x_260, 2);
lean_inc(x_288);
x_289 = lean_nat_add(x_275, x_277);
lean_inc(x_274);
if (lean_is_scalar(x_285)) {
 x_290 = lean_alloc_ctor(0, 3, 0);
} else {
 x_290 = x_285;
}
lean_ctor_set(x_290, 0, x_274);
lean_ctor_set(x_290, 1, x_289);
lean_ctor_set(x_290, 2, x_276);
x_291 = lean_nat_dec_lt(x_287, x_288);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_264)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_264;
}
lean_ctor_set(x_292, 0, x_279);
lean_ctor_set(x_292, 1, x_263);
if (lean_is_scalar(x_262)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_262;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_292);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_260);
lean_ctor_set(x_294, 1, x_293);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_13);
return x_295;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 lean_ctor_release(x_260, 2);
 x_296 = x_260;
} else {
 lean_dec_ref(x_260);
 x_296 = lean_box(0);
}
x_297 = lean_array_fget(x_265, x_266);
lean_dec(x_266);
lean_dec(x_265);
x_298 = lean_array_fget(x_274, x_275);
lean_dec(x_275);
lean_dec(x_274);
x_299 = lean_array_fget(x_286, x_287);
x_300 = lean_box(x_2);
x_301 = lean_box(x_4);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_302 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2___boxed), 14, 7);
lean_closure_set(x_302, 0, x_299);
lean_closure_set(x_302, 1, x_1);
lean_closure_set(x_302, 2, x_300);
lean_closure_set(x_302, 3, x_3);
lean_closure_set(x_302, 4, x_8);
lean_closure_set(x_302, 5, x_301);
lean_closure_set(x_302, 6, x_5);
x_303 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_303, 0, x_298);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_304 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_297, x_303, x_302, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_nat_add(x_287, x_277);
lean_dec(x_287);
if (lean_is_scalar(x_296)) {
 x_308 = lean_alloc_ctor(0, 3, 0);
} else {
 x_308 = x_296;
}
lean_ctor_set(x_308, 0, x_286);
lean_ctor_set(x_308, 1, x_307);
lean_ctor_set(x_308, 2, x_288);
x_309 = lean_array_push(x_263, x_305);
if (lean_is_scalar(x_264)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_264;
}
lean_ctor_set(x_310, 0, x_279);
lean_ctor_set(x_310, 1, x_309);
if (lean_is_scalar(x_262)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_262;
}
lean_ctor_set(x_311, 0, x_290);
lean_ctor_set(x_311, 1, x_310);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_308);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_nat_add(x_8, x_15);
lean_dec(x_8);
x_7 = x_312;
x_8 = x_313;
x_13 = x_306;
goto _start;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_296);
lean_dec(x_290);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_279);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_315 = lean_ctor_get(x_304, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_304, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_317 = x_304;
} else {
 lean_dec_ref(x_304);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_315);
lean_ctor_set(x_318, 1, x_316);
return x_318;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_7 = lean_box(0);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_30; lean_object* x_31; 
x_30 = l_Array_append___redArg(x_8, x_5);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_31 = l_Lean_Meta_instantiateLambda(x_9, x_30, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
x_17 = x_31;
goto block_29;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_38; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
x_38 = l_Lean_Exception_isInterrupt(x_32);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Lean_Exception_isRuntime(x_32);
lean_dec(x_32);
x_34 = x_39;
goto block_37;
}
else
{
lean_dec(x_32);
x_34 = x_38;
goto block_37;
}
block_37:
{
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
x_35 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2;
x_36 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_35, x_12, x_13, x_14, x_15, x_33);
x_17 = x_36;
goto block_29;
}
else
{
lean_dec(x_33);
x_17 = x_31;
goto block_29;
}
}
}
block_29:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_20 = lean_apply_8(x_1, x_2, x_11, x_18, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Array_append___redArg(x_3, x_4);
x_24 = l_Array_append___redArg(x_23, x_5);
x_25 = l_Array_append___redArg(x_24, x_10);
x_26 = lean_box(1);
x_27 = lean_unbox(x_26);
x_28 = l_Lean_Meta_mkLambdaFVars(x_25, x_21, x_6, x_7, x_6, x_27, x_12, x_13, x_14, x_15, x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_28;
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
return x_20;
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_box(x_5);
x_18 = lean_box(x_6);
x_19 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__0___boxed), 16, 9);
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
x_21 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_11, x_20, x_19, x_5, x_12, x_13, x_14, x_15, x_16);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_box(x_4);
x_18 = lean_box(x_5);
x_19 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__1___boxed), 16, 9);
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
x_21 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_11, x_20, x_19, x_4, x_12, x_13, x_14, x_15, x_16);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_17 = l_Lean_Meta_instantiateForall(x_1, x_10, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(x_4);
x_21 = lean_box(x_5);
lean_inc(x_10);
x_22 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__2___boxed), 16, 9);
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
lean_dec(x_10);
x_24 = lean_nat_sub(x_9, x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_18, x_25, x_22, x_4, x_12, x_13, x_14, x_15, x_19);
return x_26;
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_nat_dec_lt(x_9, x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_21, 0);
x_35 = lean_ctor_get(x_21, 1);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_22, 1);
x_38 = lean_ctor_get(x_22, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_23, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_23, 2);
lean_inc(x_41);
x_42 = lean_nat_dec_lt(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_14);
return x_43;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_45 = lean_ctor_get(x_23, 2);
lean_dec(x_45);
x_46 = lean_ctor_get(x_23, 1);
lean_dec(x_46);
x_47 = lean_ctor_get(x_23, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_34, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_34, 2);
lean_inc(x_50);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_40, x_51);
lean_inc(x_39);
lean_ctor_set(x_23, 1, x_52);
x_53 = lean_nat_dec_lt(x_49, x_50);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_8);
lean_ctor_set(x_54, 1, x_14);
return x_54;
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_34);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_56 = lean_ctor_get(x_34, 2);
lean_dec(x_56);
x_57 = lean_ctor_get(x_34, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_34, 0);
lean_dec(x_58);
x_59 = lean_ctor_get(x_31, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_31, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_31, 2);
lean_inc(x_61);
x_62 = lean_nat_add(x_49, x_51);
lean_inc(x_48);
lean_ctor_set(x_34, 1, x_62);
x_63 = lean_nat_dec_lt(x_60, x_61);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_8);
lean_ctor_set(x_64, 1, x_14);
return x_64;
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_31);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_66 = lean_ctor_get(x_31, 2);
lean_dec(x_66);
x_67 = lean_ctor_get(x_31, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_31, 0);
lean_dec(x_68);
x_69 = lean_ctor_get(x_28, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_28, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_28, 2);
lean_inc(x_71);
x_72 = lean_nat_add(x_60, x_51);
lean_inc(x_59);
lean_ctor_set(x_31, 1, x_72);
x_73 = lean_nat_dec_lt(x_70, x_71);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_8);
lean_ctor_set(x_74, 1, x_14);
return x_74;
}
else
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_28);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_76 = lean_ctor_get(x_28, 2);
lean_dec(x_76);
x_77 = lean_ctor_get(x_28, 1);
lean_dec(x_77);
x_78 = lean_ctor_get(x_28, 0);
lean_dec(x_78);
x_79 = lean_ctor_get(x_25, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_25, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_25, 2);
lean_inc(x_81);
x_82 = lean_nat_add(x_70, x_51);
lean_inc(x_69);
lean_ctor_set(x_28, 1, x_82);
x_83 = lean_nat_dec_lt(x_80, x_81);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_8);
lean_ctor_set(x_84, 1, x_14);
return x_84;
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_25);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_86 = lean_ctor_get(x_25, 2);
lean_dec(x_86);
x_87 = lean_ctor_get(x_25, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_25, 0);
lean_dec(x_88);
x_89 = lean_array_fget(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
x_90 = lean_array_fget(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
x_91 = lean_array_fget(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
x_92 = lean_array_fget(x_69, x_70);
lean_dec(x_70);
lean_dec(x_69);
x_93 = lean_array_fget(x_79, x_80);
x_94 = lean_box(x_2);
x_95 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_96 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_96, 0, x_89);
lean_closure_set(x_96, 1, x_1);
lean_closure_set(x_96, 2, x_9);
lean_closure_set(x_96, 3, x_94);
lean_closure_set(x_96, 4, x_95);
lean_closure_set(x_96, 5, x_93);
lean_closure_set(x_96, 6, x_4);
lean_closure_set(x_96, 7, x_5);
lean_closure_set(x_96, 8, x_91);
x_97 = lean_nat_sub(x_92, x_5);
lean_dec(x_92);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_98 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg(x_90, x_97, x_6, x_96, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_nat_add(x_80, x_51);
lean_dec(x_80);
lean_ctor_set(x_25, 1, x_101);
x_102 = lean_array_push(x_37, x_99);
lean_ctor_set(x_22, 1, x_102);
x_103 = lean_nat_add(x_9, x_16);
lean_dec(x_9);
x_9 = x_103;
x_14 = x_100;
goto _start;
}
else
{
uint8_t x_105; 
lean_free_object(x_25);
lean_dec(x_28);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_31);
lean_dec(x_34);
lean_dec(x_23);
lean_free_object(x_22);
lean_dec(x_37);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_98);
if (x_105 == 0)
{
return x_98;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_98, 0);
x_107 = lean_ctor_get(x_98, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_98);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_25);
x_109 = lean_array_fget(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
x_110 = lean_array_fget(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
x_111 = lean_array_fget(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
x_112 = lean_array_fget(x_69, x_70);
lean_dec(x_70);
lean_dec(x_69);
x_113 = lean_array_fget(x_79, x_80);
x_114 = lean_box(x_2);
x_115 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_116 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_116, 0, x_109);
lean_closure_set(x_116, 1, x_1);
lean_closure_set(x_116, 2, x_9);
lean_closure_set(x_116, 3, x_114);
lean_closure_set(x_116, 4, x_115);
lean_closure_set(x_116, 5, x_113);
lean_closure_set(x_116, 6, x_4);
lean_closure_set(x_116, 7, x_5);
lean_closure_set(x_116, 8, x_111);
x_117 = lean_nat_sub(x_112, x_5);
lean_dec(x_112);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_118 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg(x_110, x_117, x_6, x_116, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_nat_add(x_80, x_51);
lean_dec(x_80);
x_122 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_122, 0, x_79);
lean_ctor_set(x_122, 1, x_121);
lean_ctor_set(x_122, 2, x_81);
x_123 = lean_array_push(x_37, x_119);
lean_ctor_set(x_22, 1, x_123);
lean_ctor_set(x_8, 0, x_122);
x_124 = lean_nat_add(x_9, x_16);
lean_dec(x_9);
x_9 = x_124;
x_14 = x_120;
goto _start;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_28);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_31);
lean_dec(x_34);
lean_dec(x_23);
lean_free_object(x_22);
lean_dec(x_37);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_126 = lean_ctor_get(x_118, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_118, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_128 = x_118;
} else {
 lean_dec_ref(x_118);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_28);
x_130 = lean_ctor_get(x_25, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_25, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_25, 2);
lean_inc(x_132);
x_133 = lean_nat_add(x_70, x_51);
lean_inc(x_69);
x_134 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_134, 0, x_69);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_134, 2, x_71);
x_135 = lean_nat_dec_lt(x_131, x_132);
if (x_135 == 0)
{
lean_object* x_136; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_19, 0, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_8);
lean_ctor_set(x_136, 1, x_14);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_137 = x_25;
} else {
 lean_dec_ref(x_25);
 x_137 = lean_box(0);
}
x_138 = lean_array_fget(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
x_139 = lean_array_fget(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
x_140 = lean_array_fget(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
x_141 = lean_array_fget(x_69, x_70);
lean_dec(x_70);
lean_dec(x_69);
x_142 = lean_array_fget(x_130, x_131);
x_143 = lean_box(x_2);
x_144 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_145 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_145, 0, x_138);
lean_closure_set(x_145, 1, x_1);
lean_closure_set(x_145, 2, x_9);
lean_closure_set(x_145, 3, x_143);
lean_closure_set(x_145, 4, x_144);
lean_closure_set(x_145, 5, x_142);
lean_closure_set(x_145, 6, x_4);
lean_closure_set(x_145, 7, x_5);
lean_closure_set(x_145, 8, x_140);
x_146 = lean_nat_sub(x_141, x_5);
lean_dec(x_141);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_147 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg(x_139, x_146, x_6, x_145, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_nat_add(x_131, x_51);
lean_dec(x_131);
if (lean_is_scalar(x_137)) {
 x_151 = lean_alloc_ctor(0, 3, 0);
} else {
 x_151 = x_137;
}
lean_ctor_set(x_151, 0, x_130);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_151, 2, x_132);
x_152 = lean_array_push(x_37, x_148);
lean_ctor_set(x_22, 1, x_152);
lean_ctor_set(x_19, 0, x_134);
lean_ctor_set(x_8, 0, x_151);
x_153 = lean_nat_add(x_9, x_16);
lean_dec(x_9);
x_9 = x_153;
x_14 = x_149;
goto _start;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_137);
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_31);
lean_dec(x_34);
lean_dec(x_23);
lean_free_object(x_22);
lean_dec(x_37);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_155 = lean_ctor_get(x_147, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_147, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_157 = x_147;
} else {
 lean_dec_ref(x_147);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
lean_dec(x_31);
x_159 = lean_ctor_get(x_28, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_28, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_28, 2);
lean_inc(x_161);
x_162 = lean_nat_add(x_60, x_51);
lean_inc(x_59);
x_163 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_163, 0, x_59);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set(x_163, 2, x_61);
x_164 = lean_nat_dec_lt(x_160, x_161);
if (x_164 == 0)
{
lean_object* x_165; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_20, 0, x_163);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_8);
lean_ctor_set(x_165, 1, x_14);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_166 = x_28;
} else {
 lean_dec_ref(x_28);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_25, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_25, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_25, 2);
lean_inc(x_169);
x_170 = lean_nat_add(x_160, x_51);
lean_inc(x_159);
if (lean_is_scalar(x_166)) {
 x_171 = lean_alloc_ctor(0, 3, 0);
} else {
 x_171 = x_166;
}
lean_ctor_set(x_171, 0, x_159);
lean_ctor_set(x_171, 1, x_170);
lean_ctor_set(x_171, 2, x_161);
x_172 = lean_nat_dec_lt(x_168, x_169);
if (x_172 == 0)
{
lean_object* x_173; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_20, 0, x_163);
lean_ctor_set(x_19, 0, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_8);
lean_ctor_set(x_173, 1, x_14);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_174 = x_25;
} else {
 lean_dec_ref(x_25);
 x_174 = lean_box(0);
}
x_175 = lean_array_fget(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
x_176 = lean_array_fget(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
x_177 = lean_array_fget(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
x_178 = lean_array_fget(x_159, x_160);
lean_dec(x_160);
lean_dec(x_159);
x_179 = lean_array_fget(x_167, x_168);
x_180 = lean_box(x_2);
x_181 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_182 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_182, 0, x_175);
lean_closure_set(x_182, 1, x_1);
lean_closure_set(x_182, 2, x_9);
lean_closure_set(x_182, 3, x_180);
lean_closure_set(x_182, 4, x_181);
lean_closure_set(x_182, 5, x_179);
lean_closure_set(x_182, 6, x_4);
lean_closure_set(x_182, 7, x_5);
lean_closure_set(x_182, 8, x_177);
x_183 = lean_nat_sub(x_178, x_5);
lean_dec(x_178);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_184 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg(x_176, x_183, x_6, x_182, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_nat_add(x_168, x_51);
lean_dec(x_168);
if (lean_is_scalar(x_174)) {
 x_188 = lean_alloc_ctor(0, 3, 0);
} else {
 x_188 = x_174;
}
lean_ctor_set(x_188, 0, x_167);
lean_ctor_set(x_188, 1, x_187);
lean_ctor_set(x_188, 2, x_169);
x_189 = lean_array_push(x_37, x_185);
lean_ctor_set(x_22, 1, x_189);
lean_ctor_set(x_20, 0, x_163);
lean_ctor_set(x_19, 0, x_171);
lean_ctor_set(x_8, 0, x_188);
x_190 = lean_nat_add(x_9, x_16);
lean_dec(x_9);
x_9 = x_190;
x_14 = x_186;
goto _start;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_174);
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_163);
lean_dec(x_34);
lean_dec(x_23);
lean_free_object(x_22);
lean_dec(x_37);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_192 = lean_ctor_get(x_184, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_184, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_194 = x_184;
} else {
 lean_dec_ref(x_184);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
}
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
lean_dec(x_34);
x_196 = lean_ctor_get(x_31, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_31, 1);
lean_inc(x_197);
x_198 = lean_ctor_get(x_31, 2);
lean_inc(x_198);
x_199 = lean_nat_add(x_49, x_51);
lean_inc(x_48);
x_200 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_200, 0, x_48);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set(x_200, 2, x_50);
x_201 = lean_nat_dec_lt(x_197, x_198);
if (x_201 == 0)
{
lean_object* x_202; 
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_21, 0, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_8);
lean_ctor_set(x_202, 1, x_14);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_203 = x_31;
} else {
 lean_dec_ref(x_31);
 x_203 = lean_box(0);
}
x_204 = lean_ctor_get(x_28, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_28, 1);
lean_inc(x_205);
x_206 = lean_ctor_get(x_28, 2);
lean_inc(x_206);
x_207 = lean_nat_add(x_197, x_51);
lean_inc(x_196);
if (lean_is_scalar(x_203)) {
 x_208 = lean_alloc_ctor(0, 3, 0);
} else {
 x_208 = x_203;
}
lean_ctor_set(x_208, 0, x_196);
lean_ctor_set(x_208, 1, x_207);
lean_ctor_set(x_208, 2, x_198);
x_209 = lean_nat_dec_lt(x_205, x_206);
if (x_209 == 0)
{
lean_object* x_210; 
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_21, 0, x_200);
lean_ctor_set(x_20, 0, x_208);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_8);
lean_ctor_set(x_210, 1, x_14);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_211 = x_28;
} else {
 lean_dec_ref(x_28);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_25, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_25, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_25, 2);
lean_inc(x_214);
x_215 = lean_nat_add(x_205, x_51);
lean_inc(x_204);
if (lean_is_scalar(x_211)) {
 x_216 = lean_alloc_ctor(0, 3, 0);
} else {
 x_216 = x_211;
}
lean_ctor_set(x_216, 0, x_204);
lean_ctor_set(x_216, 1, x_215);
lean_ctor_set(x_216, 2, x_206);
x_217 = lean_nat_dec_lt(x_213, x_214);
if (x_217 == 0)
{
lean_object* x_218; 
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_21, 0, x_200);
lean_ctor_set(x_20, 0, x_208);
lean_ctor_set(x_19, 0, x_216);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_8);
lean_ctor_set(x_218, 1, x_14);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_219 = x_25;
} else {
 lean_dec_ref(x_25);
 x_219 = lean_box(0);
}
x_220 = lean_array_fget(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
x_221 = lean_array_fget(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
x_222 = lean_array_fget(x_196, x_197);
lean_dec(x_197);
lean_dec(x_196);
x_223 = lean_array_fget(x_204, x_205);
lean_dec(x_205);
lean_dec(x_204);
x_224 = lean_array_fget(x_212, x_213);
x_225 = lean_box(x_2);
x_226 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_227 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_227, 0, x_220);
lean_closure_set(x_227, 1, x_1);
lean_closure_set(x_227, 2, x_9);
lean_closure_set(x_227, 3, x_225);
lean_closure_set(x_227, 4, x_226);
lean_closure_set(x_227, 5, x_224);
lean_closure_set(x_227, 6, x_4);
lean_closure_set(x_227, 7, x_5);
lean_closure_set(x_227, 8, x_222);
x_228 = lean_nat_sub(x_223, x_5);
lean_dec(x_223);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_229 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg(x_221, x_228, x_6, x_227, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_nat_add(x_213, x_51);
lean_dec(x_213);
if (lean_is_scalar(x_219)) {
 x_233 = lean_alloc_ctor(0, 3, 0);
} else {
 x_233 = x_219;
}
lean_ctor_set(x_233, 0, x_212);
lean_ctor_set(x_233, 1, x_232);
lean_ctor_set(x_233, 2, x_214);
x_234 = lean_array_push(x_37, x_230);
lean_ctor_set(x_22, 1, x_234);
lean_ctor_set(x_21, 0, x_200);
lean_ctor_set(x_20, 0, x_208);
lean_ctor_set(x_19, 0, x_216);
lean_ctor_set(x_8, 0, x_233);
x_235 = lean_nat_add(x_9, x_16);
lean_dec(x_9);
x_9 = x_235;
x_14 = x_231;
goto _start;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_219);
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_208);
lean_dec(x_200);
lean_dec(x_23);
lean_free_object(x_22);
lean_dec(x_37);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_237 = lean_ctor_get(x_229, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_229, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_239 = x_229;
} else {
 lean_dec_ref(x_229);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
}
}
}
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
lean_dec(x_23);
x_241 = lean_ctor_get(x_34, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_34, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_34, 2);
lean_inc(x_243);
x_244 = lean_unsigned_to_nat(1u);
x_245 = lean_nat_add(x_40, x_244);
lean_inc(x_39);
x_246 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_246, 0, x_39);
lean_ctor_set(x_246, 1, x_245);
lean_ctor_set(x_246, 2, x_41);
x_247 = lean_nat_dec_lt(x_242, x_243);
if (x_247 == 0)
{
lean_object* x_248; 
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_22, 0, x_246);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_8);
lean_ctor_set(x_248, 1, x_14);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 x_249 = x_34;
} else {
 lean_dec_ref(x_34);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_31, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_31, 1);
lean_inc(x_251);
x_252 = lean_ctor_get(x_31, 2);
lean_inc(x_252);
x_253 = lean_nat_add(x_242, x_244);
lean_inc(x_241);
if (lean_is_scalar(x_249)) {
 x_254 = lean_alloc_ctor(0, 3, 0);
} else {
 x_254 = x_249;
}
lean_ctor_set(x_254, 0, x_241);
lean_ctor_set(x_254, 1, x_253);
lean_ctor_set(x_254, 2, x_243);
x_255 = lean_nat_dec_lt(x_251, x_252);
if (x_255 == 0)
{
lean_object* x_256; 
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_22, 0, x_246);
lean_ctor_set(x_21, 0, x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_8);
lean_ctor_set(x_256, 1, x_14);
return x_256;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_257 = x_31;
} else {
 lean_dec_ref(x_31);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_28, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_28, 1);
lean_inc(x_259);
x_260 = lean_ctor_get(x_28, 2);
lean_inc(x_260);
x_261 = lean_nat_add(x_251, x_244);
lean_inc(x_250);
if (lean_is_scalar(x_257)) {
 x_262 = lean_alloc_ctor(0, 3, 0);
} else {
 x_262 = x_257;
}
lean_ctor_set(x_262, 0, x_250);
lean_ctor_set(x_262, 1, x_261);
lean_ctor_set(x_262, 2, x_252);
x_263 = lean_nat_dec_lt(x_259, x_260);
if (x_263 == 0)
{
lean_object* x_264; 
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_22, 0, x_246);
lean_ctor_set(x_21, 0, x_254);
lean_ctor_set(x_20, 0, x_262);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_8);
lean_ctor_set(x_264, 1, x_14);
return x_264;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_265 = x_28;
} else {
 lean_dec_ref(x_28);
 x_265 = lean_box(0);
}
x_266 = lean_ctor_get(x_25, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_25, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_25, 2);
lean_inc(x_268);
x_269 = lean_nat_add(x_259, x_244);
lean_inc(x_258);
if (lean_is_scalar(x_265)) {
 x_270 = lean_alloc_ctor(0, 3, 0);
} else {
 x_270 = x_265;
}
lean_ctor_set(x_270, 0, x_258);
lean_ctor_set(x_270, 1, x_269);
lean_ctor_set(x_270, 2, x_260);
x_271 = lean_nat_dec_lt(x_267, x_268);
if (x_271 == 0)
{
lean_object* x_272; 
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_22, 0, x_246);
lean_ctor_set(x_21, 0, x_254);
lean_ctor_set(x_20, 0, x_262);
lean_ctor_set(x_19, 0, x_270);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_8);
lean_ctor_set(x_272, 1, x_14);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_273 = x_25;
} else {
 lean_dec_ref(x_25);
 x_273 = lean_box(0);
}
x_274 = lean_array_fget(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
x_275 = lean_array_fget(x_241, x_242);
lean_dec(x_242);
lean_dec(x_241);
x_276 = lean_array_fget(x_250, x_251);
lean_dec(x_251);
lean_dec(x_250);
x_277 = lean_array_fget(x_258, x_259);
lean_dec(x_259);
lean_dec(x_258);
x_278 = lean_array_fget(x_266, x_267);
x_279 = lean_box(x_2);
x_280 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_281 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_281, 0, x_274);
lean_closure_set(x_281, 1, x_1);
lean_closure_set(x_281, 2, x_9);
lean_closure_set(x_281, 3, x_279);
lean_closure_set(x_281, 4, x_280);
lean_closure_set(x_281, 5, x_278);
lean_closure_set(x_281, 6, x_4);
lean_closure_set(x_281, 7, x_5);
lean_closure_set(x_281, 8, x_276);
x_282 = lean_nat_sub(x_277, x_5);
lean_dec(x_277);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_283 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg(x_275, x_282, x_6, x_281, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_286 = lean_nat_add(x_267, x_244);
lean_dec(x_267);
if (lean_is_scalar(x_273)) {
 x_287 = lean_alloc_ctor(0, 3, 0);
} else {
 x_287 = x_273;
}
lean_ctor_set(x_287, 0, x_266);
lean_ctor_set(x_287, 1, x_286);
lean_ctor_set(x_287, 2, x_268);
x_288 = lean_array_push(x_37, x_284);
lean_ctor_set(x_22, 1, x_288);
lean_ctor_set(x_22, 0, x_246);
lean_ctor_set(x_21, 0, x_254);
lean_ctor_set(x_20, 0, x_262);
lean_ctor_set(x_19, 0, x_270);
lean_ctor_set(x_8, 0, x_287);
x_289 = lean_nat_add(x_9, x_16);
lean_dec(x_9);
x_9 = x_289;
x_14 = x_285;
goto _start;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_273);
lean_dec(x_270);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_262);
lean_dec(x_254);
lean_dec(x_246);
lean_free_object(x_22);
lean_dec(x_37);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_291 = lean_ctor_get(x_283, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_283, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_293 = x_283;
} else {
 lean_dec_ref(x_283);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_292);
return x_294;
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
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_295 = lean_ctor_get(x_22, 1);
lean_inc(x_295);
lean_dec(x_22);
x_296 = lean_ctor_get(x_23, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_23, 1);
lean_inc(x_297);
x_298 = lean_ctor_get(x_23, 2);
lean_inc(x_298);
x_299 = lean_nat_dec_lt(x_297, x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; 
lean_dec(x_298);
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_23);
lean_ctor_set(x_300, 1, x_295);
lean_ctor_set(x_21, 1, x_300);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_8);
lean_ctor_set(x_301, 1, x_14);
return x_301;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_302 = x_23;
} else {
 lean_dec_ref(x_23);
 x_302 = lean_box(0);
}
x_303 = lean_ctor_get(x_34, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_34, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_34, 2);
lean_inc(x_305);
x_306 = lean_unsigned_to_nat(1u);
x_307 = lean_nat_add(x_297, x_306);
lean_inc(x_296);
if (lean_is_scalar(x_302)) {
 x_308 = lean_alloc_ctor(0, 3, 0);
} else {
 x_308 = x_302;
}
lean_ctor_set(x_308, 0, x_296);
lean_ctor_set(x_308, 1, x_307);
lean_ctor_set(x_308, 2, x_298);
x_309 = lean_nat_dec_lt(x_304, x_305);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; 
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_295);
lean_ctor_set(x_21, 1, x_310);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_8);
lean_ctor_set(x_311, 1, x_14);
return x_311;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; 
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 x_312 = x_34;
} else {
 lean_dec_ref(x_34);
 x_312 = lean_box(0);
}
x_313 = lean_ctor_get(x_31, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_31, 1);
lean_inc(x_314);
x_315 = lean_ctor_get(x_31, 2);
lean_inc(x_315);
x_316 = lean_nat_add(x_304, x_306);
lean_inc(x_303);
if (lean_is_scalar(x_312)) {
 x_317 = lean_alloc_ctor(0, 3, 0);
} else {
 x_317 = x_312;
}
lean_ctor_set(x_317, 0, x_303);
lean_ctor_set(x_317, 1, x_316);
lean_ctor_set(x_317, 2, x_305);
x_318 = lean_nat_dec_lt(x_314, x_315);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; 
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_308);
lean_ctor_set(x_319, 1, x_295);
lean_ctor_set(x_21, 1, x_319);
lean_ctor_set(x_21, 0, x_317);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_8);
lean_ctor_set(x_320, 1, x_14);
return x_320;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_321 = x_31;
} else {
 lean_dec_ref(x_31);
 x_321 = lean_box(0);
}
x_322 = lean_ctor_get(x_28, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_28, 1);
lean_inc(x_323);
x_324 = lean_ctor_get(x_28, 2);
lean_inc(x_324);
x_325 = lean_nat_add(x_314, x_306);
lean_inc(x_313);
if (lean_is_scalar(x_321)) {
 x_326 = lean_alloc_ctor(0, 3, 0);
} else {
 x_326 = x_321;
}
lean_ctor_set(x_326, 0, x_313);
lean_ctor_set(x_326, 1, x_325);
lean_ctor_set(x_326, 2, x_315);
x_327 = lean_nat_dec_lt(x_323, x_324);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; 
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_308);
lean_ctor_set(x_328, 1, x_295);
lean_ctor_set(x_21, 1, x_328);
lean_ctor_set(x_21, 0, x_317);
lean_ctor_set(x_20, 0, x_326);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_8);
lean_ctor_set(x_329, 1, x_14);
return x_329;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; 
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_330 = x_28;
} else {
 lean_dec_ref(x_28);
 x_330 = lean_box(0);
}
x_331 = lean_ctor_get(x_25, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_25, 1);
lean_inc(x_332);
x_333 = lean_ctor_get(x_25, 2);
lean_inc(x_333);
x_334 = lean_nat_add(x_323, x_306);
lean_inc(x_322);
if (lean_is_scalar(x_330)) {
 x_335 = lean_alloc_ctor(0, 3, 0);
} else {
 x_335 = x_330;
}
lean_ctor_set(x_335, 0, x_322);
lean_ctor_set(x_335, 1, x_334);
lean_ctor_set(x_335, 2, x_324);
x_336 = lean_nat_dec_lt(x_332, x_333);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; 
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_308);
lean_ctor_set(x_337, 1, x_295);
lean_ctor_set(x_21, 1, x_337);
lean_ctor_set(x_21, 0, x_317);
lean_ctor_set(x_20, 0, x_326);
lean_ctor_set(x_19, 0, x_335);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_8);
lean_ctor_set(x_338, 1, x_14);
return x_338;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_339 = x_25;
} else {
 lean_dec_ref(x_25);
 x_339 = lean_box(0);
}
x_340 = lean_array_fget(x_296, x_297);
lean_dec(x_297);
lean_dec(x_296);
x_341 = lean_array_fget(x_303, x_304);
lean_dec(x_304);
lean_dec(x_303);
x_342 = lean_array_fget(x_313, x_314);
lean_dec(x_314);
lean_dec(x_313);
x_343 = lean_array_fget(x_322, x_323);
lean_dec(x_323);
lean_dec(x_322);
x_344 = lean_array_fget(x_331, x_332);
x_345 = lean_box(x_2);
x_346 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_347 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_347, 0, x_340);
lean_closure_set(x_347, 1, x_1);
lean_closure_set(x_347, 2, x_9);
lean_closure_set(x_347, 3, x_345);
lean_closure_set(x_347, 4, x_346);
lean_closure_set(x_347, 5, x_344);
lean_closure_set(x_347, 6, x_4);
lean_closure_set(x_347, 7, x_5);
lean_closure_set(x_347, 8, x_342);
x_348 = lean_nat_sub(x_343, x_5);
lean_dec(x_343);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_349 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg(x_341, x_348, x_6, x_347, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
x_352 = lean_nat_add(x_332, x_306);
lean_dec(x_332);
if (lean_is_scalar(x_339)) {
 x_353 = lean_alloc_ctor(0, 3, 0);
} else {
 x_353 = x_339;
}
lean_ctor_set(x_353, 0, x_331);
lean_ctor_set(x_353, 1, x_352);
lean_ctor_set(x_353, 2, x_333);
x_354 = lean_array_push(x_295, x_350);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_308);
lean_ctor_set(x_355, 1, x_354);
lean_ctor_set(x_21, 1, x_355);
lean_ctor_set(x_21, 0, x_317);
lean_ctor_set(x_20, 0, x_326);
lean_ctor_set(x_19, 0, x_335);
lean_ctor_set(x_8, 0, x_353);
x_356 = lean_nat_add(x_9, x_16);
lean_dec(x_9);
x_9 = x_356;
x_14 = x_351;
goto _start;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_339);
lean_dec(x_335);
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_326);
lean_dec(x_317);
lean_dec(x_308);
lean_dec(x_295);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_358 = lean_ctor_get(x_349, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_349, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 x_360 = x_349;
} else {
 lean_dec_ref(x_349);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_359);
return x_361;
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
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_362 = lean_ctor_get(x_21, 0);
lean_inc(x_362);
lean_dec(x_21);
x_363 = lean_ctor_get(x_22, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_364 = x_22;
} else {
 lean_dec_ref(x_22);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_23, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_23, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_23, 2);
lean_inc(x_367);
x_368 = lean_nat_dec_lt(x_366, x_367);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_367);
lean_dec(x_366);
lean_dec(x_365);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_364)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_364;
}
lean_ctor_set(x_369, 0, x_23);
lean_ctor_set(x_369, 1, x_363);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_362);
lean_ctor_set(x_370, 1, x_369);
lean_ctor_set(x_20, 1, x_370);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_8);
lean_ctor_set(x_371, 1, x_14);
return x_371;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; 
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_372 = x_23;
} else {
 lean_dec_ref(x_23);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_362, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_362, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_362, 2);
lean_inc(x_375);
x_376 = lean_unsigned_to_nat(1u);
x_377 = lean_nat_add(x_366, x_376);
lean_inc(x_365);
if (lean_is_scalar(x_372)) {
 x_378 = lean_alloc_ctor(0, 3, 0);
} else {
 x_378 = x_372;
}
lean_ctor_set(x_378, 0, x_365);
lean_ctor_set(x_378, 1, x_377);
lean_ctor_set(x_378, 2, x_367);
x_379 = lean_nat_dec_lt(x_374, x_375);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_375);
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_366);
lean_dec(x_365);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_364)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_364;
}
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_363);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_362);
lean_ctor_set(x_381, 1, x_380);
lean_ctor_set(x_20, 1, x_381);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_8);
lean_ctor_set(x_382, 1, x_14);
return x_382;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; 
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 lean_ctor_release(x_362, 2);
 x_383 = x_362;
} else {
 lean_dec_ref(x_362);
 x_383 = lean_box(0);
}
x_384 = lean_ctor_get(x_31, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_31, 1);
lean_inc(x_385);
x_386 = lean_ctor_get(x_31, 2);
lean_inc(x_386);
x_387 = lean_nat_add(x_374, x_376);
lean_inc(x_373);
if (lean_is_scalar(x_383)) {
 x_388 = lean_alloc_ctor(0, 3, 0);
} else {
 x_388 = x_383;
}
lean_ctor_set(x_388, 0, x_373);
lean_ctor_set(x_388, 1, x_387);
lean_ctor_set(x_388, 2, x_375);
x_389 = lean_nat_dec_lt(x_385, x_386);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_386);
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_366);
lean_dec(x_365);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_364)) {
 x_390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_390 = x_364;
}
lean_ctor_set(x_390, 0, x_378);
lean_ctor_set(x_390, 1, x_363);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_388);
lean_ctor_set(x_391, 1, x_390);
lean_ctor_set(x_20, 1, x_391);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_8);
lean_ctor_set(x_392, 1, x_14);
return x_392;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; 
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_393 = x_31;
} else {
 lean_dec_ref(x_31);
 x_393 = lean_box(0);
}
x_394 = lean_ctor_get(x_28, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_28, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_28, 2);
lean_inc(x_396);
x_397 = lean_nat_add(x_385, x_376);
lean_inc(x_384);
if (lean_is_scalar(x_393)) {
 x_398 = lean_alloc_ctor(0, 3, 0);
} else {
 x_398 = x_393;
}
lean_ctor_set(x_398, 0, x_384);
lean_ctor_set(x_398, 1, x_397);
lean_ctor_set(x_398, 2, x_386);
x_399 = lean_nat_dec_lt(x_395, x_396);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_394);
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_366);
lean_dec(x_365);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_364)) {
 x_400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_400 = x_364;
}
lean_ctor_set(x_400, 0, x_378);
lean_ctor_set(x_400, 1, x_363);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_388);
lean_ctor_set(x_401, 1, x_400);
lean_ctor_set(x_20, 1, x_401);
lean_ctor_set(x_20, 0, x_398);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_8);
lean_ctor_set(x_402, 1, x_14);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; 
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_403 = x_28;
} else {
 lean_dec_ref(x_28);
 x_403 = lean_box(0);
}
x_404 = lean_ctor_get(x_25, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_25, 1);
lean_inc(x_405);
x_406 = lean_ctor_get(x_25, 2);
lean_inc(x_406);
x_407 = lean_nat_add(x_395, x_376);
lean_inc(x_394);
if (lean_is_scalar(x_403)) {
 x_408 = lean_alloc_ctor(0, 3, 0);
} else {
 x_408 = x_403;
}
lean_ctor_set(x_408, 0, x_394);
lean_ctor_set(x_408, 1, x_407);
lean_ctor_set(x_408, 2, x_396);
x_409 = lean_nat_dec_lt(x_405, x_406);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_395);
lean_dec(x_394);
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_366);
lean_dec(x_365);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_364)) {
 x_410 = lean_alloc_ctor(0, 2, 0);
} else {
 x_410 = x_364;
}
lean_ctor_set(x_410, 0, x_378);
lean_ctor_set(x_410, 1, x_363);
x_411 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_411, 0, x_388);
lean_ctor_set(x_411, 1, x_410);
lean_ctor_set(x_20, 1, x_411);
lean_ctor_set(x_20, 0, x_398);
lean_ctor_set(x_19, 0, x_408);
x_412 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_412, 0, x_8);
lean_ctor_set(x_412, 1, x_14);
return x_412;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_413 = x_25;
} else {
 lean_dec_ref(x_25);
 x_413 = lean_box(0);
}
x_414 = lean_array_fget(x_365, x_366);
lean_dec(x_366);
lean_dec(x_365);
x_415 = lean_array_fget(x_373, x_374);
lean_dec(x_374);
lean_dec(x_373);
x_416 = lean_array_fget(x_384, x_385);
lean_dec(x_385);
lean_dec(x_384);
x_417 = lean_array_fget(x_394, x_395);
lean_dec(x_395);
lean_dec(x_394);
x_418 = lean_array_fget(x_404, x_405);
x_419 = lean_box(x_2);
x_420 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_421 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_421, 0, x_414);
lean_closure_set(x_421, 1, x_1);
lean_closure_set(x_421, 2, x_9);
lean_closure_set(x_421, 3, x_419);
lean_closure_set(x_421, 4, x_420);
lean_closure_set(x_421, 5, x_418);
lean_closure_set(x_421, 6, x_4);
lean_closure_set(x_421, 7, x_5);
lean_closure_set(x_421, 8, x_416);
x_422 = lean_nat_sub(x_417, x_5);
lean_dec(x_417);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_423 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg(x_415, x_422, x_6, x_421, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
lean_dec(x_423);
x_426 = lean_nat_add(x_405, x_376);
lean_dec(x_405);
if (lean_is_scalar(x_413)) {
 x_427 = lean_alloc_ctor(0, 3, 0);
} else {
 x_427 = x_413;
}
lean_ctor_set(x_427, 0, x_404);
lean_ctor_set(x_427, 1, x_426);
lean_ctor_set(x_427, 2, x_406);
x_428 = lean_array_push(x_363, x_424);
if (lean_is_scalar(x_364)) {
 x_429 = lean_alloc_ctor(0, 2, 0);
} else {
 x_429 = x_364;
}
lean_ctor_set(x_429, 0, x_378);
lean_ctor_set(x_429, 1, x_428);
x_430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_430, 0, x_388);
lean_ctor_set(x_430, 1, x_429);
lean_ctor_set(x_20, 1, x_430);
lean_ctor_set(x_20, 0, x_398);
lean_ctor_set(x_19, 0, x_408);
lean_ctor_set(x_8, 0, x_427);
x_431 = lean_nat_add(x_9, x_16);
lean_dec(x_9);
x_9 = x_431;
x_14 = x_425;
goto _start;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_413);
lean_dec(x_408);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_398);
lean_dec(x_388);
lean_dec(x_378);
lean_dec(x_364);
lean_dec(x_363);
lean_free_object(x_20);
lean_free_object(x_19);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_433 = lean_ctor_get(x_423, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_423, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_435 = x_423;
} else {
 lean_dec_ref(x_423);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_435)) {
 x_436 = lean_alloc_ctor(1, 2, 0);
} else {
 x_436 = x_435;
}
lean_ctor_set(x_436, 0, x_433);
lean_ctor_set(x_436, 1, x_434);
return x_436;
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
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; 
x_437 = lean_ctor_get(x_20, 0);
lean_inc(x_437);
lean_dec(x_20);
x_438 = lean_ctor_get(x_21, 0);
lean_inc(x_438);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_439 = x_21;
} else {
 lean_dec_ref(x_21);
 x_439 = lean_box(0);
}
x_440 = lean_ctor_get(x_22, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_441 = x_22;
} else {
 lean_dec_ref(x_22);
 x_441 = lean_box(0);
}
x_442 = lean_ctor_get(x_23, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_23, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_23, 2);
lean_inc(x_444);
x_445 = lean_nat_dec_lt(x_443, x_444);
if (x_445 == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_444);
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_441)) {
 x_446 = lean_alloc_ctor(0, 2, 0);
} else {
 x_446 = x_441;
}
lean_ctor_set(x_446, 0, x_23);
lean_ctor_set(x_446, 1, x_440);
if (lean_is_scalar(x_439)) {
 x_447 = lean_alloc_ctor(0, 2, 0);
} else {
 x_447 = x_439;
}
lean_ctor_set(x_447, 0, x_438);
lean_ctor_set(x_447, 1, x_446);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_437);
lean_ctor_set(x_448, 1, x_447);
lean_ctor_set(x_19, 1, x_448);
x_449 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_449, 0, x_8);
lean_ctor_set(x_449, 1, x_14);
return x_449;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; 
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_450 = x_23;
} else {
 lean_dec_ref(x_23);
 x_450 = lean_box(0);
}
x_451 = lean_ctor_get(x_438, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_438, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_438, 2);
lean_inc(x_453);
x_454 = lean_unsigned_to_nat(1u);
x_455 = lean_nat_add(x_443, x_454);
lean_inc(x_442);
if (lean_is_scalar(x_450)) {
 x_456 = lean_alloc_ctor(0, 3, 0);
} else {
 x_456 = x_450;
}
lean_ctor_set(x_456, 0, x_442);
lean_ctor_set(x_456, 1, x_455);
lean_ctor_set(x_456, 2, x_444);
x_457 = lean_nat_dec_lt(x_452, x_453);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_441)) {
 x_458 = lean_alloc_ctor(0, 2, 0);
} else {
 x_458 = x_441;
}
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_440);
if (lean_is_scalar(x_439)) {
 x_459 = lean_alloc_ctor(0, 2, 0);
} else {
 x_459 = x_439;
}
lean_ctor_set(x_459, 0, x_438);
lean_ctor_set(x_459, 1, x_458);
x_460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_460, 0, x_437);
lean_ctor_set(x_460, 1, x_459);
lean_ctor_set(x_19, 1, x_460);
x_461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_461, 0, x_8);
lean_ctor_set(x_461, 1, x_14);
return x_461;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; uint8_t x_468; 
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 lean_ctor_release(x_438, 2);
 x_462 = x_438;
} else {
 lean_dec_ref(x_438);
 x_462 = lean_box(0);
}
x_463 = lean_ctor_get(x_437, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_437, 1);
lean_inc(x_464);
x_465 = lean_ctor_get(x_437, 2);
lean_inc(x_465);
x_466 = lean_nat_add(x_452, x_454);
lean_inc(x_451);
if (lean_is_scalar(x_462)) {
 x_467 = lean_alloc_ctor(0, 3, 0);
} else {
 x_467 = x_462;
}
lean_ctor_set(x_467, 0, x_451);
lean_ctor_set(x_467, 1, x_466);
lean_ctor_set(x_467, 2, x_453);
x_468 = lean_nat_dec_lt(x_464, x_465);
if (x_468 == 0)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_441)) {
 x_469 = lean_alloc_ctor(0, 2, 0);
} else {
 x_469 = x_441;
}
lean_ctor_set(x_469, 0, x_456);
lean_ctor_set(x_469, 1, x_440);
if (lean_is_scalar(x_439)) {
 x_470 = lean_alloc_ctor(0, 2, 0);
} else {
 x_470 = x_439;
}
lean_ctor_set(x_470, 0, x_467);
lean_ctor_set(x_470, 1, x_469);
x_471 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_471, 0, x_437);
lean_ctor_set(x_471, 1, x_470);
lean_ctor_set(x_19, 1, x_471);
x_472 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_472, 0, x_8);
lean_ctor_set(x_472, 1, x_14);
return x_472;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; 
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 lean_ctor_release(x_437, 2);
 x_473 = x_437;
} else {
 lean_dec_ref(x_437);
 x_473 = lean_box(0);
}
x_474 = lean_ctor_get(x_28, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_28, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_28, 2);
lean_inc(x_476);
x_477 = lean_nat_add(x_464, x_454);
lean_inc(x_463);
if (lean_is_scalar(x_473)) {
 x_478 = lean_alloc_ctor(0, 3, 0);
} else {
 x_478 = x_473;
}
lean_ctor_set(x_478, 0, x_463);
lean_ctor_set(x_478, 1, x_477);
lean_ctor_set(x_478, 2, x_465);
x_479 = lean_nat_dec_lt(x_475, x_476);
if (x_479 == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_dec(x_476);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_441)) {
 x_480 = lean_alloc_ctor(0, 2, 0);
} else {
 x_480 = x_441;
}
lean_ctor_set(x_480, 0, x_456);
lean_ctor_set(x_480, 1, x_440);
if (lean_is_scalar(x_439)) {
 x_481 = lean_alloc_ctor(0, 2, 0);
} else {
 x_481 = x_439;
}
lean_ctor_set(x_481, 0, x_467);
lean_ctor_set(x_481, 1, x_480);
x_482 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_482, 0, x_478);
lean_ctor_set(x_482, 1, x_481);
lean_ctor_set(x_19, 1, x_482);
x_483 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_483, 0, x_8);
lean_ctor_set(x_483, 1, x_14);
return x_483;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; 
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_484 = x_28;
} else {
 lean_dec_ref(x_28);
 x_484 = lean_box(0);
}
x_485 = lean_ctor_get(x_25, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_25, 1);
lean_inc(x_486);
x_487 = lean_ctor_get(x_25, 2);
lean_inc(x_487);
x_488 = lean_nat_add(x_475, x_454);
lean_inc(x_474);
if (lean_is_scalar(x_484)) {
 x_489 = lean_alloc_ctor(0, 3, 0);
} else {
 x_489 = x_484;
}
lean_ctor_set(x_489, 0, x_474);
lean_ctor_set(x_489, 1, x_488);
lean_ctor_set(x_489, 2, x_476);
x_490 = lean_nat_dec_lt(x_486, x_487);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_441)) {
 x_491 = lean_alloc_ctor(0, 2, 0);
} else {
 x_491 = x_441;
}
lean_ctor_set(x_491, 0, x_456);
lean_ctor_set(x_491, 1, x_440);
if (lean_is_scalar(x_439)) {
 x_492 = lean_alloc_ctor(0, 2, 0);
} else {
 x_492 = x_439;
}
lean_ctor_set(x_492, 0, x_467);
lean_ctor_set(x_492, 1, x_491);
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_478);
lean_ctor_set(x_493, 1, x_492);
lean_ctor_set(x_19, 1, x_493);
lean_ctor_set(x_19, 0, x_489);
x_494 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_494, 0, x_8);
lean_ctor_set(x_494, 1, x_14);
return x_494;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_495 = x_25;
} else {
 lean_dec_ref(x_25);
 x_495 = lean_box(0);
}
x_496 = lean_array_fget(x_442, x_443);
lean_dec(x_443);
lean_dec(x_442);
x_497 = lean_array_fget(x_451, x_452);
lean_dec(x_452);
lean_dec(x_451);
x_498 = lean_array_fget(x_463, x_464);
lean_dec(x_464);
lean_dec(x_463);
x_499 = lean_array_fget(x_474, x_475);
lean_dec(x_475);
lean_dec(x_474);
x_500 = lean_array_fget(x_485, x_486);
x_501 = lean_box(x_2);
x_502 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_503 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_503, 0, x_496);
lean_closure_set(x_503, 1, x_1);
lean_closure_set(x_503, 2, x_9);
lean_closure_set(x_503, 3, x_501);
lean_closure_set(x_503, 4, x_502);
lean_closure_set(x_503, 5, x_500);
lean_closure_set(x_503, 6, x_4);
lean_closure_set(x_503, 7, x_5);
lean_closure_set(x_503, 8, x_498);
x_504 = lean_nat_sub(x_499, x_5);
lean_dec(x_499);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_505 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg(x_497, x_504, x_6, x_503, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
x_508 = lean_nat_add(x_486, x_454);
lean_dec(x_486);
if (lean_is_scalar(x_495)) {
 x_509 = lean_alloc_ctor(0, 3, 0);
} else {
 x_509 = x_495;
}
lean_ctor_set(x_509, 0, x_485);
lean_ctor_set(x_509, 1, x_508);
lean_ctor_set(x_509, 2, x_487);
x_510 = lean_array_push(x_440, x_506);
if (lean_is_scalar(x_441)) {
 x_511 = lean_alloc_ctor(0, 2, 0);
} else {
 x_511 = x_441;
}
lean_ctor_set(x_511, 0, x_456);
lean_ctor_set(x_511, 1, x_510);
if (lean_is_scalar(x_439)) {
 x_512 = lean_alloc_ctor(0, 2, 0);
} else {
 x_512 = x_439;
}
lean_ctor_set(x_512, 0, x_467);
lean_ctor_set(x_512, 1, x_511);
x_513 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_513, 0, x_478);
lean_ctor_set(x_513, 1, x_512);
lean_ctor_set(x_19, 1, x_513);
lean_ctor_set(x_19, 0, x_489);
lean_ctor_set(x_8, 0, x_509);
x_514 = lean_nat_add(x_9, x_16);
lean_dec(x_9);
x_9 = x_514;
x_14 = x_507;
goto _start;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
lean_dec(x_495);
lean_dec(x_489);
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_478);
lean_dec(x_467);
lean_dec(x_456);
lean_dec(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_free_object(x_19);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_516 = lean_ctor_get(x_505, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_505, 1);
lean_inc(x_517);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_518 = x_505;
} else {
 lean_dec_ref(x_505);
 x_518 = lean_box(0);
}
if (lean_is_scalar(x_518)) {
 x_519 = lean_alloc_ctor(1, 2, 0);
} else {
 x_519 = x_518;
}
lean_ctor_set(x_519, 0, x_516);
lean_ctor_set(x_519, 1, x_517);
return x_519;
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
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; uint8_t x_530; 
x_520 = lean_ctor_get(x_19, 0);
lean_inc(x_520);
lean_dec(x_19);
x_521 = lean_ctor_get(x_20, 0);
lean_inc(x_521);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_522 = x_20;
} else {
 lean_dec_ref(x_20);
 x_522 = lean_box(0);
}
x_523 = lean_ctor_get(x_21, 0);
lean_inc(x_523);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_524 = x_21;
} else {
 lean_dec_ref(x_21);
 x_524 = lean_box(0);
}
x_525 = lean_ctor_get(x_22, 1);
lean_inc(x_525);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_526 = x_22;
} else {
 lean_dec_ref(x_22);
 x_526 = lean_box(0);
}
x_527 = lean_ctor_get(x_23, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_23, 1);
lean_inc(x_528);
x_529 = lean_ctor_get(x_23, 2);
lean_inc(x_529);
x_530 = lean_nat_dec_lt(x_528, x_529);
if (x_530 == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_529);
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_526)) {
 x_531 = lean_alloc_ctor(0, 2, 0);
} else {
 x_531 = x_526;
}
lean_ctor_set(x_531, 0, x_23);
lean_ctor_set(x_531, 1, x_525);
if (lean_is_scalar(x_524)) {
 x_532 = lean_alloc_ctor(0, 2, 0);
} else {
 x_532 = x_524;
}
lean_ctor_set(x_532, 0, x_523);
lean_ctor_set(x_532, 1, x_531);
if (lean_is_scalar(x_522)) {
 x_533 = lean_alloc_ctor(0, 2, 0);
} else {
 x_533 = x_522;
}
lean_ctor_set(x_533, 0, x_521);
lean_ctor_set(x_533, 1, x_532);
x_534 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_534, 0, x_520);
lean_ctor_set(x_534, 1, x_533);
lean_ctor_set(x_8, 1, x_534);
x_535 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_535, 0, x_8);
lean_ctor_set(x_535, 1, x_14);
return x_535;
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; uint8_t x_543; 
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_536 = x_23;
} else {
 lean_dec_ref(x_23);
 x_536 = lean_box(0);
}
x_537 = lean_ctor_get(x_523, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_523, 1);
lean_inc(x_538);
x_539 = lean_ctor_get(x_523, 2);
lean_inc(x_539);
x_540 = lean_unsigned_to_nat(1u);
x_541 = lean_nat_add(x_528, x_540);
lean_inc(x_527);
if (lean_is_scalar(x_536)) {
 x_542 = lean_alloc_ctor(0, 3, 0);
} else {
 x_542 = x_536;
}
lean_ctor_set(x_542, 0, x_527);
lean_ctor_set(x_542, 1, x_541);
lean_ctor_set(x_542, 2, x_529);
x_543 = lean_nat_dec_lt(x_538, x_539);
if (x_543 == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_526)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_526;
}
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_525);
if (lean_is_scalar(x_524)) {
 x_545 = lean_alloc_ctor(0, 2, 0);
} else {
 x_545 = x_524;
}
lean_ctor_set(x_545, 0, x_523);
lean_ctor_set(x_545, 1, x_544);
if (lean_is_scalar(x_522)) {
 x_546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_546 = x_522;
}
lean_ctor_set(x_546, 0, x_521);
lean_ctor_set(x_546, 1, x_545);
x_547 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_547, 0, x_520);
lean_ctor_set(x_547, 1, x_546);
lean_ctor_set(x_8, 1, x_547);
x_548 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_548, 0, x_8);
lean_ctor_set(x_548, 1, x_14);
return x_548;
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; uint8_t x_555; 
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 lean_ctor_release(x_523, 1);
 lean_ctor_release(x_523, 2);
 x_549 = x_523;
} else {
 lean_dec_ref(x_523);
 x_549 = lean_box(0);
}
x_550 = lean_ctor_get(x_521, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_521, 1);
lean_inc(x_551);
x_552 = lean_ctor_get(x_521, 2);
lean_inc(x_552);
x_553 = lean_nat_add(x_538, x_540);
lean_inc(x_537);
if (lean_is_scalar(x_549)) {
 x_554 = lean_alloc_ctor(0, 3, 0);
} else {
 x_554 = x_549;
}
lean_ctor_set(x_554, 0, x_537);
lean_ctor_set(x_554, 1, x_553);
lean_ctor_set(x_554, 2, x_539);
x_555 = lean_nat_dec_lt(x_551, x_552);
if (x_555 == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_526)) {
 x_556 = lean_alloc_ctor(0, 2, 0);
} else {
 x_556 = x_526;
}
lean_ctor_set(x_556, 0, x_542);
lean_ctor_set(x_556, 1, x_525);
if (lean_is_scalar(x_524)) {
 x_557 = lean_alloc_ctor(0, 2, 0);
} else {
 x_557 = x_524;
}
lean_ctor_set(x_557, 0, x_554);
lean_ctor_set(x_557, 1, x_556);
if (lean_is_scalar(x_522)) {
 x_558 = lean_alloc_ctor(0, 2, 0);
} else {
 x_558 = x_522;
}
lean_ctor_set(x_558, 0, x_521);
lean_ctor_set(x_558, 1, x_557);
x_559 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_559, 0, x_520);
lean_ctor_set(x_559, 1, x_558);
lean_ctor_set(x_8, 1, x_559);
x_560 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_560, 0, x_8);
lean_ctor_set(x_560, 1, x_14);
return x_560;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; uint8_t x_567; 
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 lean_ctor_release(x_521, 1);
 lean_ctor_release(x_521, 2);
 x_561 = x_521;
} else {
 lean_dec_ref(x_521);
 x_561 = lean_box(0);
}
x_562 = lean_ctor_get(x_520, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_520, 1);
lean_inc(x_563);
x_564 = lean_ctor_get(x_520, 2);
lean_inc(x_564);
x_565 = lean_nat_add(x_551, x_540);
lean_inc(x_550);
if (lean_is_scalar(x_561)) {
 x_566 = lean_alloc_ctor(0, 3, 0);
} else {
 x_566 = x_561;
}
lean_ctor_set(x_566, 0, x_550);
lean_ctor_set(x_566, 1, x_565);
lean_ctor_set(x_566, 2, x_552);
x_567 = lean_nat_dec_lt(x_563, x_564);
if (x_567 == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
lean_dec(x_564);
lean_dec(x_563);
lean_dec(x_562);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_526)) {
 x_568 = lean_alloc_ctor(0, 2, 0);
} else {
 x_568 = x_526;
}
lean_ctor_set(x_568, 0, x_542);
lean_ctor_set(x_568, 1, x_525);
if (lean_is_scalar(x_524)) {
 x_569 = lean_alloc_ctor(0, 2, 0);
} else {
 x_569 = x_524;
}
lean_ctor_set(x_569, 0, x_554);
lean_ctor_set(x_569, 1, x_568);
if (lean_is_scalar(x_522)) {
 x_570 = lean_alloc_ctor(0, 2, 0);
} else {
 x_570 = x_522;
}
lean_ctor_set(x_570, 0, x_566);
lean_ctor_set(x_570, 1, x_569);
x_571 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_571, 0, x_520);
lean_ctor_set(x_571, 1, x_570);
lean_ctor_set(x_8, 1, x_571);
x_572 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_572, 0, x_8);
lean_ctor_set(x_572, 1, x_14);
return x_572;
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; uint8_t x_579; 
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 lean_ctor_release(x_520, 1);
 lean_ctor_release(x_520, 2);
 x_573 = x_520;
} else {
 lean_dec_ref(x_520);
 x_573 = lean_box(0);
}
x_574 = lean_ctor_get(x_25, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_25, 1);
lean_inc(x_575);
x_576 = lean_ctor_get(x_25, 2);
lean_inc(x_576);
x_577 = lean_nat_add(x_563, x_540);
lean_inc(x_562);
if (lean_is_scalar(x_573)) {
 x_578 = lean_alloc_ctor(0, 3, 0);
} else {
 x_578 = x_573;
}
lean_ctor_set(x_578, 0, x_562);
lean_ctor_set(x_578, 1, x_577);
lean_ctor_set(x_578, 2, x_564);
x_579 = lean_nat_dec_lt(x_575, x_576);
if (x_579 == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; 
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_574);
lean_dec(x_563);
lean_dec(x_562);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_526)) {
 x_580 = lean_alloc_ctor(0, 2, 0);
} else {
 x_580 = x_526;
}
lean_ctor_set(x_580, 0, x_542);
lean_ctor_set(x_580, 1, x_525);
if (lean_is_scalar(x_524)) {
 x_581 = lean_alloc_ctor(0, 2, 0);
} else {
 x_581 = x_524;
}
lean_ctor_set(x_581, 0, x_554);
lean_ctor_set(x_581, 1, x_580);
if (lean_is_scalar(x_522)) {
 x_582 = lean_alloc_ctor(0, 2, 0);
} else {
 x_582 = x_522;
}
lean_ctor_set(x_582, 0, x_566);
lean_ctor_set(x_582, 1, x_581);
x_583 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_583, 0, x_578);
lean_ctor_set(x_583, 1, x_582);
lean_ctor_set(x_8, 1, x_583);
x_584 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_584, 0, x_8);
lean_ctor_set(x_584, 1, x_14);
return x_584;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_585 = x_25;
} else {
 lean_dec_ref(x_25);
 x_585 = lean_box(0);
}
x_586 = lean_array_fget(x_527, x_528);
lean_dec(x_528);
lean_dec(x_527);
x_587 = lean_array_fget(x_537, x_538);
lean_dec(x_538);
lean_dec(x_537);
x_588 = lean_array_fget(x_550, x_551);
lean_dec(x_551);
lean_dec(x_550);
x_589 = lean_array_fget(x_562, x_563);
lean_dec(x_563);
lean_dec(x_562);
x_590 = lean_array_fget(x_574, x_575);
x_591 = lean_box(x_2);
x_592 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_593 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_593, 0, x_586);
lean_closure_set(x_593, 1, x_1);
lean_closure_set(x_593, 2, x_9);
lean_closure_set(x_593, 3, x_591);
lean_closure_set(x_593, 4, x_592);
lean_closure_set(x_593, 5, x_590);
lean_closure_set(x_593, 6, x_4);
lean_closure_set(x_593, 7, x_5);
lean_closure_set(x_593, 8, x_588);
x_594 = lean_nat_sub(x_589, x_5);
lean_dec(x_589);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_595 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg(x_587, x_594, x_6, x_593, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_595) == 0)
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_595, 1);
lean_inc(x_597);
lean_dec(x_595);
x_598 = lean_nat_add(x_575, x_540);
lean_dec(x_575);
if (lean_is_scalar(x_585)) {
 x_599 = lean_alloc_ctor(0, 3, 0);
} else {
 x_599 = x_585;
}
lean_ctor_set(x_599, 0, x_574);
lean_ctor_set(x_599, 1, x_598);
lean_ctor_set(x_599, 2, x_576);
x_600 = lean_array_push(x_525, x_596);
if (lean_is_scalar(x_526)) {
 x_601 = lean_alloc_ctor(0, 2, 0);
} else {
 x_601 = x_526;
}
lean_ctor_set(x_601, 0, x_542);
lean_ctor_set(x_601, 1, x_600);
if (lean_is_scalar(x_524)) {
 x_602 = lean_alloc_ctor(0, 2, 0);
} else {
 x_602 = x_524;
}
lean_ctor_set(x_602, 0, x_554);
lean_ctor_set(x_602, 1, x_601);
if (lean_is_scalar(x_522)) {
 x_603 = lean_alloc_ctor(0, 2, 0);
} else {
 x_603 = x_522;
}
lean_ctor_set(x_603, 0, x_566);
lean_ctor_set(x_603, 1, x_602);
x_604 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_604, 0, x_578);
lean_ctor_set(x_604, 1, x_603);
lean_ctor_set(x_8, 1, x_604);
lean_ctor_set(x_8, 0, x_599);
x_605 = lean_nat_add(x_9, x_16);
lean_dec(x_9);
x_9 = x_605;
x_14 = x_597;
goto _start;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_585);
lean_dec(x_578);
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_574);
lean_dec(x_566);
lean_dec(x_554);
lean_dec(x_542);
lean_dec(x_526);
lean_dec(x_525);
lean_dec(x_524);
lean_dec(x_522);
lean_free_object(x_8);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_607 = lean_ctor_get(x_595, 0);
lean_inc(x_607);
x_608 = lean_ctor_get(x_595, 1);
lean_inc(x_608);
if (lean_is_exclusive(x_595)) {
 lean_ctor_release(x_595, 0);
 lean_ctor_release(x_595, 1);
 x_609 = x_595;
} else {
 lean_dec_ref(x_595);
 x_609 = lean_box(0);
}
if (lean_is_scalar(x_609)) {
 x_610 = lean_alloc_ctor(1, 2, 0);
} else {
 x_610 = x_609;
}
lean_ctor_set(x_610, 0, x_607);
lean_ctor_set(x_610, 1, x_608);
return x_610;
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
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; uint8_t x_623; 
x_611 = lean_ctor_get(x_8, 0);
lean_inc(x_611);
lean_dec(x_8);
x_612 = lean_ctor_get(x_19, 0);
lean_inc(x_612);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_613 = x_19;
} else {
 lean_dec_ref(x_19);
 x_613 = lean_box(0);
}
x_614 = lean_ctor_get(x_20, 0);
lean_inc(x_614);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_615 = x_20;
} else {
 lean_dec_ref(x_20);
 x_615 = lean_box(0);
}
x_616 = lean_ctor_get(x_21, 0);
lean_inc(x_616);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_617 = x_21;
} else {
 lean_dec_ref(x_21);
 x_617 = lean_box(0);
}
x_618 = lean_ctor_get(x_22, 1);
lean_inc(x_618);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_619 = x_22;
} else {
 lean_dec_ref(x_22);
 x_619 = lean_box(0);
}
x_620 = lean_ctor_get(x_23, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_23, 1);
lean_inc(x_621);
x_622 = lean_ctor_get(x_23, 2);
lean_inc(x_622);
x_623 = lean_nat_dec_lt(x_621, x_622);
if (x_623 == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_622);
lean_dec(x_621);
lean_dec(x_620);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_619)) {
 x_624 = lean_alloc_ctor(0, 2, 0);
} else {
 x_624 = x_619;
}
lean_ctor_set(x_624, 0, x_23);
lean_ctor_set(x_624, 1, x_618);
if (lean_is_scalar(x_617)) {
 x_625 = lean_alloc_ctor(0, 2, 0);
} else {
 x_625 = x_617;
}
lean_ctor_set(x_625, 0, x_616);
lean_ctor_set(x_625, 1, x_624);
if (lean_is_scalar(x_615)) {
 x_626 = lean_alloc_ctor(0, 2, 0);
} else {
 x_626 = x_615;
}
lean_ctor_set(x_626, 0, x_614);
lean_ctor_set(x_626, 1, x_625);
if (lean_is_scalar(x_613)) {
 x_627 = lean_alloc_ctor(0, 2, 0);
} else {
 x_627 = x_613;
}
lean_ctor_set(x_627, 0, x_612);
lean_ctor_set(x_627, 1, x_626);
x_628 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_628, 0, x_611);
lean_ctor_set(x_628, 1, x_627);
x_629 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_629, 0, x_628);
lean_ctor_set(x_629, 1, x_14);
return x_629;
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; uint8_t x_637; 
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_630 = x_23;
} else {
 lean_dec_ref(x_23);
 x_630 = lean_box(0);
}
x_631 = lean_ctor_get(x_616, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_616, 1);
lean_inc(x_632);
x_633 = lean_ctor_get(x_616, 2);
lean_inc(x_633);
x_634 = lean_unsigned_to_nat(1u);
x_635 = lean_nat_add(x_621, x_634);
lean_inc(x_620);
if (lean_is_scalar(x_630)) {
 x_636 = lean_alloc_ctor(0, 3, 0);
} else {
 x_636 = x_630;
}
lean_ctor_set(x_636, 0, x_620);
lean_ctor_set(x_636, 1, x_635);
lean_ctor_set(x_636, 2, x_622);
x_637 = lean_nat_dec_lt(x_632, x_633);
if (x_637 == 0)
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_633);
lean_dec(x_632);
lean_dec(x_631);
lean_dec(x_621);
lean_dec(x_620);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_619)) {
 x_638 = lean_alloc_ctor(0, 2, 0);
} else {
 x_638 = x_619;
}
lean_ctor_set(x_638, 0, x_636);
lean_ctor_set(x_638, 1, x_618);
if (lean_is_scalar(x_617)) {
 x_639 = lean_alloc_ctor(0, 2, 0);
} else {
 x_639 = x_617;
}
lean_ctor_set(x_639, 0, x_616);
lean_ctor_set(x_639, 1, x_638);
if (lean_is_scalar(x_615)) {
 x_640 = lean_alloc_ctor(0, 2, 0);
} else {
 x_640 = x_615;
}
lean_ctor_set(x_640, 0, x_614);
lean_ctor_set(x_640, 1, x_639);
if (lean_is_scalar(x_613)) {
 x_641 = lean_alloc_ctor(0, 2, 0);
} else {
 x_641 = x_613;
}
lean_ctor_set(x_641, 0, x_612);
lean_ctor_set(x_641, 1, x_640);
x_642 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_642, 0, x_611);
lean_ctor_set(x_642, 1, x_641);
x_643 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_14);
return x_643;
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; uint8_t x_650; 
if (lean_is_exclusive(x_616)) {
 lean_ctor_release(x_616, 0);
 lean_ctor_release(x_616, 1);
 lean_ctor_release(x_616, 2);
 x_644 = x_616;
} else {
 lean_dec_ref(x_616);
 x_644 = lean_box(0);
}
x_645 = lean_ctor_get(x_614, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_614, 1);
lean_inc(x_646);
x_647 = lean_ctor_get(x_614, 2);
lean_inc(x_647);
x_648 = lean_nat_add(x_632, x_634);
lean_inc(x_631);
if (lean_is_scalar(x_644)) {
 x_649 = lean_alloc_ctor(0, 3, 0);
} else {
 x_649 = x_644;
}
lean_ctor_set(x_649, 0, x_631);
lean_ctor_set(x_649, 1, x_648);
lean_ctor_set(x_649, 2, x_633);
x_650 = lean_nat_dec_lt(x_646, x_647);
if (x_650 == 0)
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_dec(x_647);
lean_dec(x_646);
lean_dec(x_645);
lean_dec(x_632);
lean_dec(x_631);
lean_dec(x_621);
lean_dec(x_620);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_619)) {
 x_651 = lean_alloc_ctor(0, 2, 0);
} else {
 x_651 = x_619;
}
lean_ctor_set(x_651, 0, x_636);
lean_ctor_set(x_651, 1, x_618);
if (lean_is_scalar(x_617)) {
 x_652 = lean_alloc_ctor(0, 2, 0);
} else {
 x_652 = x_617;
}
lean_ctor_set(x_652, 0, x_649);
lean_ctor_set(x_652, 1, x_651);
if (lean_is_scalar(x_615)) {
 x_653 = lean_alloc_ctor(0, 2, 0);
} else {
 x_653 = x_615;
}
lean_ctor_set(x_653, 0, x_614);
lean_ctor_set(x_653, 1, x_652);
if (lean_is_scalar(x_613)) {
 x_654 = lean_alloc_ctor(0, 2, 0);
} else {
 x_654 = x_613;
}
lean_ctor_set(x_654, 0, x_612);
lean_ctor_set(x_654, 1, x_653);
x_655 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_655, 0, x_611);
lean_ctor_set(x_655, 1, x_654);
x_656 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_656, 0, x_655);
lean_ctor_set(x_656, 1, x_14);
return x_656;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; uint8_t x_663; 
if (lean_is_exclusive(x_614)) {
 lean_ctor_release(x_614, 0);
 lean_ctor_release(x_614, 1);
 lean_ctor_release(x_614, 2);
 x_657 = x_614;
} else {
 lean_dec_ref(x_614);
 x_657 = lean_box(0);
}
x_658 = lean_ctor_get(x_612, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_612, 1);
lean_inc(x_659);
x_660 = lean_ctor_get(x_612, 2);
lean_inc(x_660);
x_661 = lean_nat_add(x_646, x_634);
lean_inc(x_645);
if (lean_is_scalar(x_657)) {
 x_662 = lean_alloc_ctor(0, 3, 0);
} else {
 x_662 = x_657;
}
lean_ctor_set(x_662, 0, x_645);
lean_ctor_set(x_662, 1, x_661);
lean_ctor_set(x_662, 2, x_647);
x_663 = lean_nat_dec_lt(x_659, x_660);
if (x_663 == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
lean_dec(x_660);
lean_dec(x_659);
lean_dec(x_658);
lean_dec(x_646);
lean_dec(x_645);
lean_dec(x_632);
lean_dec(x_631);
lean_dec(x_621);
lean_dec(x_620);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_619)) {
 x_664 = lean_alloc_ctor(0, 2, 0);
} else {
 x_664 = x_619;
}
lean_ctor_set(x_664, 0, x_636);
lean_ctor_set(x_664, 1, x_618);
if (lean_is_scalar(x_617)) {
 x_665 = lean_alloc_ctor(0, 2, 0);
} else {
 x_665 = x_617;
}
lean_ctor_set(x_665, 0, x_649);
lean_ctor_set(x_665, 1, x_664);
if (lean_is_scalar(x_615)) {
 x_666 = lean_alloc_ctor(0, 2, 0);
} else {
 x_666 = x_615;
}
lean_ctor_set(x_666, 0, x_662);
lean_ctor_set(x_666, 1, x_665);
if (lean_is_scalar(x_613)) {
 x_667 = lean_alloc_ctor(0, 2, 0);
} else {
 x_667 = x_613;
}
lean_ctor_set(x_667, 0, x_612);
lean_ctor_set(x_667, 1, x_666);
x_668 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_668, 0, x_611);
lean_ctor_set(x_668, 1, x_667);
x_669 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_669, 0, x_668);
lean_ctor_set(x_669, 1, x_14);
return x_669;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; uint8_t x_676; 
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 lean_ctor_release(x_612, 2);
 x_670 = x_612;
} else {
 lean_dec_ref(x_612);
 x_670 = lean_box(0);
}
x_671 = lean_ctor_get(x_611, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_611, 1);
lean_inc(x_672);
x_673 = lean_ctor_get(x_611, 2);
lean_inc(x_673);
x_674 = lean_nat_add(x_659, x_634);
lean_inc(x_658);
if (lean_is_scalar(x_670)) {
 x_675 = lean_alloc_ctor(0, 3, 0);
} else {
 x_675 = x_670;
}
lean_ctor_set(x_675, 0, x_658);
lean_ctor_set(x_675, 1, x_674);
lean_ctor_set(x_675, 2, x_660);
x_676 = lean_nat_dec_lt(x_672, x_673);
if (x_676 == 0)
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
lean_dec(x_673);
lean_dec(x_672);
lean_dec(x_671);
lean_dec(x_659);
lean_dec(x_658);
lean_dec(x_646);
lean_dec(x_645);
lean_dec(x_632);
lean_dec(x_631);
lean_dec(x_621);
lean_dec(x_620);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_619)) {
 x_677 = lean_alloc_ctor(0, 2, 0);
} else {
 x_677 = x_619;
}
lean_ctor_set(x_677, 0, x_636);
lean_ctor_set(x_677, 1, x_618);
if (lean_is_scalar(x_617)) {
 x_678 = lean_alloc_ctor(0, 2, 0);
} else {
 x_678 = x_617;
}
lean_ctor_set(x_678, 0, x_649);
lean_ctor_set(x_678, 1, x_677);
if (lean_is_scalar(x_615)) {
 x_679 = lean_alloc_ctor(0, 2, 0);
} else {
 x_679 = x_615;
}
lean_ctor_set(x_679, 0, x_662);
lean_ctor_set(x_679, 1, x_678);
if (lean_is_scalar(x_613)) {
 x_680 = lean_alloc_ctor(0, 2, 0);
} else {
 x_680 = x_613;
}
lean_ctor_set(x_680, 0, x_675);
lean_ctor_set(x_680, 1, x_679);
x_681 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_681, 0, x_611);
lean_ctor_set(x_681, 1, x_680);
x_682 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_682, 0, x_681);
lean_ctor_set(x_682, 1, x_14);
return x_682;
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
if (lean_is_exclusive(x_611)) {
 lean_ctor_release(x_611, 0);
 lean_ctor_release(x_611, 1);
 lean_ctor_release(x_611, 2);
 x_683 = x_611;
} else {
 lean_dec_ref(x_611);
 x_683 = lean_box(0);
}
x_684 = lean_array_fget(x_620, x_621);
lean_dec(x_621);
lean_dec(x_620);
x_685 = lean_array_fget(x_631, x_632);
lean_dec(x_632);
lean_dec(x_631);
x_686 = lean_array_fget(x_645, x_646);
lean_dec(x_646);
lean_dec(x_645);
x_687 = lean_array_fget(x_658, x_659);
lean_dec(x_659);
lean_dec(x_658);
x_688 = lean_array_fget(x_671, x_672);
x_689 = lean_box(x_2);
x_690 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_691 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed), 16, 9);
lean_closure_set(x_691, 0, x_684);
lean_closure_set(x_691, 1, x_1);
lean_closure_set(x_691, 2, x_9);
lean_closure_set(x_691, 3, x_689);
lean_closure_set(x_691, 4, x_690);
lean_closure_set(x_691, 5, x_688);
lean_closure_set(x_691, 6, x_4);
lean_closure_set(x_691, 7, x_5);
lean_closure_set(x_691, 8, x_686);
x_692 = lean_nat_sub(x_687, x_5);
lean_dec(x_687);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_693 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg(x_685, x_692, x_6, x_691, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_693, 1);
lean_inc(x_695);
lean_dec(x_693);
x_696 = lean_nat_add(x_672, x_634);
lean_dec(x_672);
if (lean_is_scalar(x_683)) {
 x_697 = lean_alloc_ctor(0, 3, 0);
} else {
 x_697 = x_683;
}
lean_ctor_set(x_697, 0, x_671);
lean_ctor_set(x_697, 1, x_696);
lean_ctor_set(x_697, 2, x_673);
x_698 = lean_array_push(x_618, x_694);
if (lean_is_scalar(x_619)) {
 x_699 = lean_alloc_ctor(0, 2, 0);
} else {
 x_699 = x_619;
}
lean_ctor_set(x_699, 0, x_636);
lean_ctor_set(x_699, 1, x_698);
if (lean_is_scalar(x_617)) {
 x_700 = lean_alloc_ctor(0, 2, 0);
} else {
 x_700 = x_617;
}
lean_ctor_set(x_700, 0, x_649);
lean_ctor_set(x_700, 1, x_699);
if (lean_is_scalar(x_615)) {
 x_701 = lean_alloc_ctor(0, 2, 0);
} else {
 x_701 = x_615;
}
lean_ctor_set(x_701, 0, x_662);
lean_ctor_set(x_701, 1, x_700);
if (lean_is_scalar(x_613)) {
 x_702 = lean_alloc_ctor(0, 2, 0);
} else {
 x_702 = x_613;
}
lean_ctor_set(x_702, 0, x_675);
lean_ctor_set(x_702, 1, x_701);
x_703 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_703, 0, x_697);
lean_ctor_set(x_703, 1, x_702);
x_704 = lean_nat_add(x_9, x_16);
lean_dec(x_9);
x_8 = x_703;
x_9 = x_704;
x_14 = x_695;
goto _start;
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
lean_dec(x_683);
lean_dec(x_675);
lean_dec(x_673);
lean_dec(x_672);
lean_dec(x_671);
lean_dec(x_662);
lean_dec(x_649);
lean_dec(x_636);
lean_dec(x_619);
lean_dec(x_618);
lean_dec(x_617);
lean_dec(x_615);
lean_dec(x_613);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_706 = lean_ctor_get(x_693, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_693, 1);
lean_inc(x_707);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_708 = x_693;
} else {
 lean_dec_ref(x_693);
 x_708 = lean_box(0);
}
if (lean_is_scalar(x_708)) {
 x_709 = lean_alloc_ctor(1, 2, 0);
} else {
 x_709 = x_708;
}
lean_ctor_set(x_709, 0, x_706);
lean_ctor_set(x_709, 1, x_707);
return x_709;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12, x_13, x_14, x_15, x_16);
return x_17;
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
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_14 = lean_apply_7(x_1, x_2, x_3, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Meta_MatcherApp_transform___redArg___lam__18___closed__0;
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
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
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
lean_dec(x_27);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
x_37 = lean_box(0);
x_38 = lean_box(1);
x_39 = lean_box(1);
x_40 = lean_unbox(x_37);
x_41 = lean_unbox(x_38);
x_42 = lean_unbox(x_37);
x_43 = lean_unbox(x_39);
lean_inc(x_36);
x_44 = l_Lean_Meta_mkLambdaFVars(x_2, x_36, x_40, x_41, x_42, x_43, x_9, x_10, x_11, x_12, x_33);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_getLevel(x_36, x_9, x_10, x_11, x_12, x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_ctor_set(x_31, 1, x_35);
lean_ctor_set(x_31, 0, x_49);
lean_ctor_set(x_29, 0, x_45);
lean_ctor_set(x_47, 0, x_29);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_47, 0);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_47);
lean_ctor_set(x_31, 1, x_35);
lean_ctor_set(x_31, 0, x_50);
lean_ctor_set(x_29, 0, x_45);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_29);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_45);
lean_free_object(x_31);
lean_dec(x_35);
lean_free_object(x_29);
x_53 = !lean_is_exclusive(x_47);
if (x_53 == 0)
{
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_47, 0);
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_47);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_free_object(x_31);
lean_dec(x_36);
lean_dec(x_35);
lean_free_object(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_57 = !lean_is_exclusive(x_44);
if (x_57 == 0)
{
return x_44;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_44, 0);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_44);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_31, 0);
x_62 = lean_ctor_get(x_31, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_31);
x_63 = lean_box(0);
x_64 = lean_box(1);
x_65 = lean_box(1);
x_66 = lean_unbox(x_63);
x_67 = lean_unbox(x_64);
x_68 = lean_unbox(x_63);
x_69 = lean_unbox(x_65);
lean_inc(x_62);
x_70 = l_Lean_Meta_mkLambdaFVars(x_2, x_62, x_66, x_67, x_68, x_69, x_9, x_10, x_11, x_12, x_33);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Meta_getLevel(x_62, x_9, x_10, x_11, x_12, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_61);
lean_ctor_set(x_29, 1, x_77);
lean_ctor_set(x_29, 0, x_71);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_29);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_71);
lean_dec(x_61);
lean_free_object(x_29);
x_79 = lean_ctor_get(x_73, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_73, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_81 = x_73;
} else {
 lean_dec_ref(x_73);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_62);
lean_dec(x_61);
lean_free_object(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_83 = lean_ctor_get(x_70, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_70, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_85 = x_70;
} else {
 lean_dec_ref(x_70);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; lean_object* x_99; 
x_87 = lean_ctor_get(x_29, 1);
lean_inc(x_87);
lean_dec(x_29);
x_88 = lean_ctor_get(x_27, 1);
lean_inc(x_88);
lean_dec(x_27);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_91 = x_87;
} else {
 lean_dec_ref(x_87);
 x_91 = lean_box(0);
}
x_92 = lean_box(0);
x_93 = lean_box(1);
x_94 = lean_box(1);
x_95 = lean_unbox(x_92);
x_96 = lean_unbox(x_93);
x_97 = lean_unbox(x_92);
x_98 = lean_unbox(x_94);
lean_inc(x_90);
x_99 = l_Lean_Meta_mkLambdaFVars(x_2, x_90, x_95, x_96, x_97, x_98, x_9, x_10, x_11, x_12, x_88);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_Meta_getLevel(x_90, x_9, x_10, x_11, x_12, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_91;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_89);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_100);
lean_ctor_set(x_107, 1, x_106);
if (lean_is_scalar(x_105)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_105;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_104);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_100);
lean_dec(x_91);
lean_dec(x_89);
x_109 = lean_ctor_get(x_102, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_102, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_111 = x_102;
} else {
 lean_dec_ref(x_102);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_113 = lean_ctor_get(x_99, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_99, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_115 = x_99;
} else {
 lean_dec_ref(x_99);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_117 = !lean_is_exclusive(x_27);
if (x_117 == 0)
{
return x_27;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_27, 0);
x_119 = lean_ctor_get(x_27, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_27);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_14);
if (x_121 == 0)
{
return x_14;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_14, 0);
x_123 = lean_ctor_get(x_14, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_14);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Meta_MatcherApp_addArg___lam__1___closed__4;
x_18 = l_Nat_reprFast(x_15);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_MessageData_ofFormat(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Meta_MatcherApp_addArg___lam__1___closed__6;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_23, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, size_t x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27) {
_start:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_array_get_size(x_1);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_28);
x_29 = l_Lean_Meta_inferArgumentTypesN(x_28, x_2, x_23, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_28);
lean_inc(x_3);
x_32 = l_Array_toSubarray___redArg(x_1, x_3, x_28);
x_33 = lean_array_get_size(x_4);
lean_inc(x_3);
lean_inc(x_4);
x_34 = l_Array_toSubarray___redArg(x_4, x_3, x_33);
x_35 = lean_array_get_size(x_30);
lean_inc(x_3);
x_36 = l_Array_toSubarray___redArg(x_30, x_3, x_35);
x_37 = lean_unsigned_to_nat(1u);
lean_inc(x_3);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_3);
lean_ctor_set(x_38, 1, x_28);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_5);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_10);
x_42 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg(x_6, x_7, x_8, x_9, x_10, x_38, x_41, x_3, x_23, x_24, x_25, x_26, x_31);
lean_dec(x_38);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_apply_6(x_11, x_12, x_23, x_24, x_25, x_26, x_46);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; size_t x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = l_Array_append___redArg(x_21, x_50);
lean_dec(x_50);
x_52 = lean_array_size(x_4);
x_53 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12(x_10, x_52, x_13, x_4);
lean_dec(x_10);
x_54 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_54, 0, x_14);
lean_ctor_set(x_54, 1, x_15);
lean_ctor_set(x_54, 2, x_16);
lean_ctor_set(x_54, 3, x_17);
lean_ctor_set(x_54, 4, x_18);
lean_ctor_set(x_54, 5, x_19);
lean_ctor_set(x_54, 6, x_20);
lean_ctor_set(x_54, 7, x_53);
lean_ctor_set(x_54, 8, x_47);
lean_ctor_set(x_54, 9, x_51);
lean_ctor_set(x_48, 0, x_54);
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_48, 0);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_48);
x_57 = l_Array_append___redArg(x_21, x_55);
lean_dec(x_55);
x_58 = lean_array_size(x_4);
x_59 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12(x_10, x_58, x_13, x_4);
lean_dec(x_10);
x_60 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_60, 0, x_14);
lean_ctor_set(x_60, 1, x_15);
lean_ctor_set(x_60, 2, x_16);
lean_ctor_set(x_60, 3, x_17);
lean_ctor_set(x_60, 4, x_18);
lean_ctor_set(x_60, 5, x_19);
lean_ctor_set(x_60, 6, x_20);
lean_ctor_set(x_60, 7, x_59);
lean_ctor_set(x_60, 8, x_47);
lean_ctor_set(x_60, 9, x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_47);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_4);
x_62 = !lean_is_exclusive(x_48);
if (x_62 == 0)
{
return x_48;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_48, 0);
x_64 = lean_ctor_get(x_48, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_48);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_66 = !lean_is_exclusive(x_42);
if (x_66 == 0)
{
return x_42;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_42, 0);
x_68 = lean_ctor_get(x_42, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_42);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_29);
if (x_70 == 0)
{
return x_29;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_29, 0);
x_72 = lean_ctor_get(x_29, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_29);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, size_t x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30) {
_start:
{
lean_object* x_31; 
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_1);
x_31 = l_Lean_Meta_inferArgumentTypesN(x_1, x_2, x_26, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_1);
lean_inc(x_4);
x_34 = l_Array_toSubarray___redArg(x_3, x_4, x_1);
x_35 = lean_array_get_size(x_5);
lean_inc(x_4);
x_36 = l_Array_toSubarray___redArg(x_5, x_4, x_35);
x_37 = lean_array_get_size(x_6);
lean_inc(x_4);
lean_inc(x_6);
x_38 = l_Array_toSubarray___redArg(x_6, x_4, x_37);
x_39 = lean_array_get_size(x_7);
lean_inc(x_4);
x_40 = l_Array_toSubarray___redArg(x_7, x_4, x_39);
x_41 = lean_array_get_size(x_32);
lean_inc(x_4);
x_42 = l_Array_toSubarray___redArg(x_32, x_4, x_41);
x_43 = lean_unsigned_to_nat(1u);
lean_inc(x_4);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_1);
lean_ctor_set(x_44, 2, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_8);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_36);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_34);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_4);
lean_inc(x_12);
x_50 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg(x_9, x_10, x_11, x_12, x_13, x_4, x_44, x_49, x_4, x_26, x_27, x_28, x_29, x_33);
lean_dec(x_44);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_apply_6(x_14, x_15, x_26, x_27, x_28, x_29, x_56);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; size_t x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = l_Array_append___redArg(x_24, x_60);
lean_dec(x_60);
x_62 = lean_array_size(x_6);
x_63 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12(x_12, x_62, x_16, x_6);
lean_dec(x_12);
x_64 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_64, 0, x_17);
lean_ctor_set(x_64, 1, x_18);
lean_ctor_set(x_64, 2, x_19);
lean_ctor_set(x_64, 3, x_20);
lean_ctor_set(x_64, 4, x_21);
lean_ctor_set(x_64, 5, x_22);
lean_ctor_set(x_64, 6, x_23);
lean_ctor_set(x_64, 7, x_63);
lean_ctor_set(x_64, 8, x_57);
lean_ctor_set(x_64, 9, x_61);
lean_ctor_set(x_58, 0, x_64);
return x_58;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; size_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_58, 0);
x_66 = lean_ctor_get(x_58, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_58);
x_67 = l_Array_append___redArg(x_24, x_65);
lean_dec(x_65);
x_68 = lean_array_size(x_6);
x_69 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12(x_12, x_68, x_16, x_6);
lean_dec(x_12);
x_70 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_70, 0, x_17);
lean_ctor_set(x_70, 1, x_18);
lean_ctor_set(x_70, 2, x_19);
lean_ctor_set(x_70, 3, x_20);
lean_ctor_set(x_70, 4, x_21);
lean_ctor_set(x_70, 5, x_22);
lean_ctor_set(x_70, 6, x_23);
lean_ctor_set(x_70, 7, x_69);
lean_ctor_set(x_70, 8, x_57);
lean_ctor_set(x_70, 9, x_67);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_66);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_57);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_6);
x_72 = !lean_is_exclusive(x_58);
if (x_72 == 0)
{
return x_58;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_58, 0);
x_74 = lean_ctor_get(x_58, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_58);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_6);
x_76 = !lean_is_exclusive(x_50);
if (x_76 == 0)
{
return x_50;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_50, 0);
x_78 = lean_ctor_get(x_50, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_50);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_31);
if (x_80 == 0)
{
return x_31;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_31, 0);
x_82 = lean_ctor_get(x_31, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_31);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, uint8_t x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, size_t x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28) {
_start:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_array_get_size(x_1);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_29);
x_30 = l_Lean_Meta_inferArgumentTypesN(x_29, x_2, x_24, x_25, x_26, x_27, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_33 = lean_get_match_equations_for(x_3, x_24, x_25, x_26, x_27, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 2);
lean_inc(x_37);
lean_dec(x_34);
lean_inc(x_36);
x_38 = l_Lean_Expr_const___override(x_36, x_4);
x_39 = l_Lean_mkAppN(x_38, x_5);
lean_inc(x_6);
x_40 = l_Lean_Expr_app___override(x_39, x_6);
x_41 = l_Lean_mkAppN(x_40, x_7);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_41);
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
lean_dec(x_42);
x_46 = l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1;
lean_inc(x_41);
x_47 = l_Lean_indentExpr(x_41);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54), 2, 1);
lean_closure_set(x_51, 0, x_50);
lean_inc(x_41);
x_52 = lean_alloc_closure((void*)(l_Lean_Meta_check), 6, 1);
lean_closure_set(x_52, 0, x_41);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_53 = l_Lean_Meta_mapErrorImp___redArg(x_52, x_51, x_24, x_25, x_26, x_27, x_45);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__4(x_29, x_41, x_1, x_8, x_9, x_37, x_31, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_36, x_19, x_20, x_21, x_5, x_6, x_7, x_22, x_54, x_24, x_25, x_26, x_27, x_55);
lean_dec(x_54);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_42);
x_62 = lean_box(0);
x_63 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__4(x_29, x_41, x_1, x_8, x_9, x_37, x_31, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_36, x_19, x_20, x_21, x_5, x_6, x_7, x_22, x_62, x_24, x_25, x_26, x_27, x_61);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, uint8_t x_16, uint8_t x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24) {
_start:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__0;
x_27 = l_Array_reverse___redArg(x_1);
x_28 = lean_array_get_size(x_27);
x_29 = l_Array_toSubarray___redArg(x_27, x_25, x_28);
lean_inc(x_2);
x_30 = l_Array_reverse___redArg(x_2);
x_31 = l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__1;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_array_size(x_30);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_34 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__8(x_30, x_33, x_3, x_32, x_20, x_21, x_22, x_23, x_24);
lean_dec(x_30);
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
lean_dec(x_34);
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
goto block_75;
}
else
{
if (x_17 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_9);
lean_inc(x_19);
x_76 = lean_array_to_list(x_19);
lean_inc(x_76);
lean_inc(x_4);
x_77 = l_Lean_Expr_const___override(x_4, x_76);
x_78 = l_Lean_mkAppN(x_77, x_5);
lean_inc(x_6);
x_79 = l_Lean_Expr_app___override(x_78, x_6);
x_80 = l_Lean_mkAppN(x_79, x_2);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_80);
x_81 = l_Lean_Meta_isTypeCorrect(x_80, x_20, x_21, x_22, x_23, x_38);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1;
lean_inc(x_80);
x_86 = l_Lean_indentExpr(x_80);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3;
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54), 2, 1);
lean_closure_set(x_90, 0, x_89);
lean_inc(x_80);
x_91 = lean_alloc_closure((void*)(l_Lean_Meta_check), 6, 1);
lean_closure_set(x_91, 0, x_80);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_92 = l_Lean_Meta_mapErrorImp___redArg(x_91, x_90, x_20, x_21, x_22, x_23, x_84);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__6(x_7, x_80, x_4, x_76, x_5, x_6, x_2, x_25, x_8, x_26, x_11, x_10, x_16, x_39, x_18, x_12, x_13, x_3, x_19, x_14, x_15, x_40, x_93, x_20, x_21, x_22, x_23, x_94);
lean_dec(x_93);
return x_95;
}
else
{
uint8_t x_96; 
lean_dec(x_80);
lean_dec(x_76);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_92);
if (x_96 == 0)
{
return x_92;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_92, 0);
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_92);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_81, 1);
lean_inc(x_100);
lean_dec(x_81);
x_101 = lean_box(0);
x_102 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__6(x_7, x_80, x_4, x_76, x_5, x_6, x_2, x_25, x_8, x_26, x_11, x_10, x_16, x_39, x_18, x_12, x_13, x_3, x_19, x_14, x_15, x_40, x_101, x_20, x_21, x_22, x_23, x_100);
return x_102;
}
}
else
{
uint8_t x_103; 
lean_dec(x_80);
lean_dec(x_76);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_81);
if (x_103 == 0)
{
return x_81;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_81, 0);
x_105 = lean_ctor_get(x_81, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_81);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
lean_dec(x_18);
goto block_75;
}
}
block_75:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_inc(x_19);
x_42 = lean_array_to_list(x_19);
lean_inc(x_4);
x_43 = l_Lean_Expr_const___override(x_4, x_42);
x_44 = l_Lean_mkAppN(x_43, x_5);
lean_inc(x_6);
x_45 = l_Lean_Expr_app___override(x_44, x_6);
x_46 = l_Lean_mkAppN(x_45, x_2);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_46);
x_47 = l_Lean_Meta_isTypeCorrect(x_46, x_20, x_21, x_22, x_23, x_38);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_box(1);
x_51 = lean_unbox(x_48);
lean_dec(x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__1;
lean_inc(x_46);
x_53 = l_Lean_indentExpr(x_46);
if (lean_is_scalar(x_41)) {
 x_54 = lean_alloc_ctor(7, 2, 0);
} else {
 x_54 = x_41;
 lean_ctor_set_tag(x_54, 7);
}
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__3;
if (lean_is_scalar(x_37)) {
 x_56 = lean_alloc_ctor(7, 2, 0);
} else {
 x_56 = x_37;
 lean_ctor_set_tag(x_56, 7);
}
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_22);
x_57 = l_Lean_logError___at___Lean_inferDefEqAttr_spec__1(x_56, x_20, x_21, x_22, x_23, x_49);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_46);
x_59 = l_Lean_Meta_check(x_46, x_20, x_21, x_22, x_23, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_unbox(x_50);
x_63 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__3(x_7, x_46, x_25, x_8, x_26, x_9, x_10, x_11, x_62, x_39, x_12, x_13, x_3, x_4, x_19, x_14, x_15, x_5, x_6, x_2, x_40, x_60, x_20, x_21, x_22, x_23, x_61);
lean_dec(x_60);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_46);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
return x_59;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_59, 0);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_59);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; 
lean_dec(x_41);
lean_dec(x_37);
x_68 = lean_box(0);
x_69 = lean_unbox(x_50);
x_70 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__3(x_7, x_46, x_25, x_8, x_26, x_9, x_10, x_11, x_69, x_39, x_12, x_13, x_3, x_4, x_19, x_14, x_15, x_5, x_6, x_2, x_40, x_68, x_20, x_21, x_22, x_23, x_49);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_47);
if (x_71 == 0)
{
return x_47;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_47, 0);
x_73 = lean_ctor_get(x_47, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_47);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_107 = !lean_is_exclusive(x_34);
if (x_107 == 0)
{
return x_34;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_34, 0);
x_109 = lean_ctor_get(x_34, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_34);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, uint8_t x_16, uint8_t x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24) {
_start:
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = lean_array_size(x_1);
x_26 = 0;
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_2);
x_27 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__6(x_2, x_25, x_26, x_1, x_20, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_array_size(x_3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_3);
x_31 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__6(x_2, x_30, x_26, x_3, x_20, x_21, x_22, x_23, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_box(x_6);
x_35 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5___boxed__const__1;
lean_inc(x_5);
lean_inc(x_32);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__2___boxed), 13, 6);
lean_closure_set(x_36, 0, x_4);
lean_closure_set(x_36, 1, x_32);
lean_closure_set(x_36, 2, x_5);
lean_closure_set(x_36, 3, x_34);
lean_closure_set(x_36, 4, x_35);
lean_closure_set(x_36, 5, x_3);
x_37 = lean_box(0);
x_38 = lean_unbox(x_37);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_39 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_7, x_36, x_38, x_20, x_21, x_22, x_23, x_33);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_unbox(x_37);
x_46 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7(x_44, x_32, x_26, x_8, x_28, x_43, x_9, x_10, x_11, x_45, x_12, x_13, x_14, x_15, x_5, x_16, x_17, x_19, x_18, x_20, x_21, x_22, x_23, x_42);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_dec(x_39);
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
lean_dec(x_40);
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec(x_41);
x_51 = lean_ctor_get(x_15, 0);
lean_inc(x_51);
x_52 = lean_array_set(x_18, x_51, x_49);
lean_dec(x_51);
x_53 = lean_unbox(x_37);
x_54 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7(x_50, x_32, x_26, x_8, x_28, x_48, x_9, x_10, x_11, x_53, x_12, x_13, x_14, x_15, x_5, x_16, x_17, x_19, x_52, x_20, x_21, x_22, x_23, x_47);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_55 = !lean_is_exclusive(x_39);
if (x_55 == 0)
{
return x_39;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_39, 0);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_39);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_59 = !lean_is_exclusive(x_31);
if (x_59 == 0)
{
return x_31;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_31, 0);
x_61 = lean_ctor_get(x_31, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_31);
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
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_27);
if (x_63 == 0)
{
return x_27;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_27, 0);
x_65 = lean_ctor_get(x_27, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_27);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
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
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 5);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 6);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 7);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 8);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 9);
lean_inc(x_27);
lean_dec(x_1);
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
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
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
x_35 = l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__1;
x_36 = l_Lean_MessageData_ofName(x_18);
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_36);
lean_ctor_set(x_30, 0, x_35);
x_37 = l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__3;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_37);
lean_ctor_set(x_13, 0, x_30);
x_38 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_13, x_8, x_9, x_10, x_11, x_33);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
x_44 = l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__1;
x_45 = l_Lean_MessageData_ofName(x_18);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__3;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_47);
lean_ctor_set(x_13, 0, x_46);
x_48 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_13, x_8, x_9, x_10, x_11, x_43);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_dec(x_30);
x_54 = lean_ctor_get(x_31, 0);
lean_inc(x_54);
lean_dec(x_31);
x_55 = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(x_54);
lean_dec(x_54);
x_56 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5(x_22, x_4, x_24, x_5, x_21, x_3, x_23, x_18, x_26, x_25, x_28, x_6, x_7, x_27, x_20, x_2, x_29, x_19, x_55, x_8, x_9, x_10, x_11, x_53);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_free_object(x_13);
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5(x_22, x_4, x_24, x_5, x_21, x_3, x_23, x_18, x_26, x_25, x_28, x_6, x_7, x_27, x_20, x_2, x_29, x_19, x_57, x_8, x_9, x_10, x_11, x_16);
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
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 4);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 5);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 6);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 7);
lean_inc(x_69);
x_70 = lean_ctor_get(x_1, 8);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 9);
lean_inc(x_71);
lean_dec(x_1);
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
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
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
x_78 = l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__1;
x_79 = l_Lean_MessageData_ofName(x_62);
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(7, 2, 0);
} else {
 x_80 = x_77;
 lean_ctor_set_tag(x_80, 7);
}
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__3;
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_82, x_8, x_9, x_10, x_11, x_76);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_dec(x_74);
x_89 = lean_ctor_get(x_75, 0);
lean_inc(x_89);
lean_dec(x_75);
x_90 = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(x_89);
lean_dec(x_89);
x_91 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5(x_66, x_4, x_68, x_5, x_65, x_3, x_67, x_62, x_70, x_69, x_72, x_6, x_7, x_71, x_64, x_2, x_73, x_63, x_90, x_8, x_9, x_10, x_11, x_88);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_unsigned_to_nat(0u);
x_93 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5(x_66, x_4, x_68, x_5, x_65, x_3, x_67, x_62, x_70, x_69, x_72, x_6, x_7, x_71, x_64, x_2, x_73, x_63, x_92, x_8, x_9, x_10, x_11, x_60);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = lean_infer_type(x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Meta_mkEq(x_3, x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
lean_inc(x_5);
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_30 = l_Lean_Meta_Split_simpMatchTarget(x_29, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
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
x_42 = l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__3;
if (lean_is_scalar(x_20)) {
 x_43 = lean_alloc_ctor(7, 2, 0);
} else {
 x_43 = x_20;
 lean_ctor_set_tag(x_43, 7);
}
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_42);
lean_inc(x_7);
x_44 = l_Lean_logInfo___at___Lean_Meta_reportDiag_spec__0(x_43, x_5, x_6, x_7, x_8, x_35);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
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
x_50 = l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__3;
if (lean_is_scalar(x_20)) {
 x_51 = lean_alloc_ctor(7, 2, 0);
} else {
 x_51 = x_20;
 lean_ctor_set_tag(x_51, 7);
}
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_7);
x_52 = l_Lean_logInfo___at___Lean_Meta_reportDiag_spec__0(x_51, x_5, x_6, x_7, x_8, x_35);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_21);
x_23 = l_Lean_Meta_mkEqMPR(x_18, x_4, x_5, x_6, x_7, x_8, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
x_18 = l_Lean_Meta_arrowDomainsN(x_1, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0;
x_22 = lean_box(1);
x_23 = lean_unbox(x_22);
lean_inc(x_11);
x_24 = l_Lean_Meta_mkLambdaFVars(x_11, x_21, x_2, x_3, x_2, x_23, x_13, x_14, x_15, x_16, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; uint8_t x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_size(x_4);
x_28 = 0;
x_29 = lean_unbox(x_22);
lean_inc(x_16);
lean_inc(x_15);
x_30 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3(x_1, x_2, x_3, x_29, x_27, x_28, x_4, x_13, x_14, x_15, x_16, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
if (lean_obj_tag(x_6) == 0)
{
x_33 = x_10;
x_34 = x_15;
x_35 = x_16;
goto block_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_6, 0);
lean_inc(x_41);
x_42 = l_Lean_levelOne;
x_43 = lean_array_set(x_10, x_41, x_42);
lean_dec(x_41);
x_33 = x_43;
x_34 = x_15;
x_35 = x_16;
goto block_40;
}
block_40:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__0;
x_37 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_6);
lean_ctor_set(x_37, 3, x_7);
lean_ctor_set(x_37, 4, x_8);
lean_ctor_set(x_37, 5, x_25);
lean_ctor_set(x_37, 6, x_11);
lean_ctor_set(x_37, 7, x_9);
lean_ctor_set(x_37, 8, x_31);
lean_ctor_set(x_37, 9, x_36);
x_38 = l_Lean_Meta_MatcherApp_toExpr(x_37);
x_39 = l_Lean_mkArrowN(x_19, x_38, x_34, x_35, x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_19);
return x_39;
}
}
else
{
uint8_t x_44; 
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_44 = !lean_is_exclusive(x_30);
if (x_44 == 0)
{
return x_30;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_30, 0);
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_30);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_24;
}
}
else
{
uint8_t x_48; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_18);
if (x_48 == 0)
{
return x_18;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_18, 0);
x_50 = lean_ctor_get(x_18, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_18);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 7);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 8);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 9);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed), 6, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed), 6, 0);
x_17 = lean_array_get_size(x_14);
lean_dec(x_14);
x_18 = lean_box(1);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed), 9, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed), 17, 10);
lean_closure_set(x_21, 0, x_17);
lean_closure_set(x_21, 1, x_20);
lean_closure_set(x_21, 2, x_18);
lean_closure_set(x_21, 3, x_13);
lean_closure_set(x_21, 4, x_7);
lean_closure_set(x_21, 5, x_9);
lean_closure_set(x_21, 6, x_10);
lean_closure_set(x_21, 7, x_11);
lean_closure_set(x_21, 8, x_12);
lean_closure_set(x_21, 9, x_8);
x_22 = lean_unbox(x_18);
x_23 = lean_unbox(x_20);
x_24 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5(x_1, x_22, x_23, x_15, x_21, x_19, x_16, x_2, x_3, x_4, x_5, x_6);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_MatcherApp_inferMatchType_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___lam__0(x_1, x_2, x_13, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3_spec__3(x_1, x_13, x_14, x_15, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_inferMatchType_spec__3(x_1, x_13, x_14, x_15, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12);
return x_18;
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
lean_dec(x_5);
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
lean_dec(x_6);
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
lean_dec(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__7(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
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
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__9___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_MatcherApp_withUserNames___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_7);
lean_dec(x_7);
x_15 = lean_unbox(x_8);
lean_dec(x_8);
x_16 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_14, x_15, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = lean_unbox(x_7);
lean_dec(x_7);
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__1(x_1, x_2, x_15, x_4, x_5, x_6, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___lam__2(x_1, x_2, x_15, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___redArg(x_1, x_14, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__11(x_1, x_16, x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__12(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = lean_unbox(x_6);
lean_dec(x_6);
x_19 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__1(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__2(x_1, x_2, x_3, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___lam__3(x_1, x_2, x_3, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___redArg(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5_spec__13(x_1, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__1(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__2(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
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
uint8_t x_28; uint8_t x_29; size_t x_30; lean_object* x_31; 
x_28 = lean_unbox(x_7);
lean_dec(x_7);
x_29 = lean_unbox(x_9);
lean_dec(x_9);
x_30 = lean_unbox_usize(x_13);
lean_dec(x_13);
x_31 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_28, x_8, x_29, x_10, x_11, x_12, x_30, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
lean_dec(x_22);
return x_31;
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
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
_start:
{
uint8_t x_31; uint8_t x_32; size_t x_33; lean_object* x_34; 
x_31 = lean_unbox(x_10);
lean_dec(x_10);
x_32 = lean_unbox(x_11);
lean_dec(x_11);
x_33 = lean_unbox_usize(x_16);
lean_dec(x_16);
x_34 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_31, x_32, x_12, x_13, x_14, x_15, x_33, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
lean_dec(x_25);
return x_34;
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
_start:
{
uint8_t x_29; uint8_t x_30; size_t x_31; lean_object* x_32; 
x_29 = lean_unbox(x_12);
lean_dec(x_12);
x_30 = lean_unbox(x_13);
lean_dec(x_13);
x_31 = lean_unbox_usize(x_18);
lean_dec(x_18);
x_32 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_29, x_30, x_14, x_15, x_16, x_17, x_31, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
lean_dec(x_23);
return x_32;
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
size_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_26 = lean_unbox(x_10);
lean_dec(x_10);
x_27 = lean_unbox(x_16);
lean_dec(x_16);
x_28 = lean_unbox(x_17);
lean_dec(x_17);
x_29 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__7(x_1, x_2, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_26, x_11, x_12, x_13, x_14, x_15, x_27, x_28, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
return x_29;
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
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
_start:
{
uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_25 = lean_unbox(x_6);
lean_dec(x_6);
x_26 = lean_unbox(x_16);
lean_dec(x_16);
x_27 = lean_unbox(x_17);
lean_dec(x_17);
x_28 = l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5(x_1, x_2, x_3, x_4, x_5, x_25, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_26, x_27, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_MatcherApp_inferMatchType___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
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
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_2);
lean_dec(x_2);
x_19 = lean_unbox(x_3);
lean_dec(x_3);
x_20 = l_Lean_Meta_MatcherApp_inferMatchType___lam__3(x_1, x_18, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_20;
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
l_Lean_Meta_MatcherApp_addArg___lam__1___closed__0 = _init_l_Lean_Meta_MatcherApp_addArg___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lam__1___closed__0);
l_Lean_Meta_MatcherApp_addArg___lam__1___closed__1 = _init_l_Lean_Meta_MatcherApp_addArg___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lam__1___closed__1);
l_Lean_Meta_MatcherApp_addArg___lam__1___closed__2 = _init_l_Lean_Meta_MatcherApp_addArg___lam__1___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lam__1___closed__2);
l_Lean_Meta_MatcherApp_addArg___lam__1___closed__3 = _init_l_Lean_Meta_MatcherApp_addArg___lam__1___closed__3();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lam__1___closed__3);
l_Lean_Meta_MatcherApp_addArg___lam__1___closed__4 = _init_l_Lean_Meta_MatcherApp_addArg___lam__1___closed__4();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lam__1___closed__4);
l_Lean_Meta_MatcherApp_addArg___lam__1___closed__5 = _init_l_Lean_Meta_MatcherApp_addArg___lam__1___closed__5();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lam__1___closed__5);
l_Lean_Meta_MatcherApp_addArg___lam__1___closed__6 = _init_l_Lean_Meta_MatcherApp_addArg___lam__1___closed__6();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lam__1___closed__6);
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
l_Lean_Meta_MatcherApp_transform___redArg___lam__18___closed__0 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__18___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__18___closed__0);
l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__0 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__0);
l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__1 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__1);
l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__2 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__2);
l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__3 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__3();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__3);
l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__4 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__4();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__4);
l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__5 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__5();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__5);
l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__6 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__6();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__6);
l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__7 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__7();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__7);
l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__8 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__8();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__8);
l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__9 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__9();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___closed__9);
l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__0 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__0);
l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__1 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__1);
l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__2 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__2);
l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__3 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__3();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___closed__3);
l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0);
l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1);
l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__2 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__2);
l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3);
l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0);
l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__0 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__0);
l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__1 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__60___closed__1);
l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__0 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__0();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__0);
l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__1 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__1);
l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__2 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__2);
l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__3 = _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__3();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___redArg___lam__69___closed__3);
l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__0 = _init_l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__0();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__0);
l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__1 = _init_l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__1();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__1);
l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__2 = _init_l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__2();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__2);
l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__3 = _init_l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__3();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__3);
l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__4 = _init_l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__4();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__4);
l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__5 = _init_l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__5();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at___Subarray_forInUnsafe_loop___at___Lean_Meta_MatcherApp_inferMatchType_spec__1_spec__1___closed__5);
l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5___boxed__const__1 = _init_l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_transform___at___Lean_Meta_MatcherApp_inferMatchType_spec__5___lam__5___boxed__const__1);
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
