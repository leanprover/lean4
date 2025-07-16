// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Simp
// Imports: Init.Grind.Lemmas Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Simp.Main Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.MatchDiscrOnly Lean.Meta.Tactic.Grind.MarkNestedSubsingletons Lean.Meta.Tactic.Grind.Canon
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
static lean_object* l_Lean_Meta_Grind_simpCore___lam__1___closed__15;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_replacePreMatchCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4_spec__4___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible_x27___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__1___closed__9;
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_preprocess___closed__5;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__9;
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__1___closed__8;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__1___closed__11;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__4;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__1___closed__0;
lean_object* l_Lean_Meta_Simp_mainCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isGrindGadget(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__7;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__1;
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__6;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__1___closed__3;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__1___closed__6;
static lean_object* l_Lean_Meta_Grind_preprocess___closed__2;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___boxed__const__1;
lean_object* l_Lean_Meta_Simp_dsimpMainCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_dsimpCore___closed__0;
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_preprocess___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_inShareCommon_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isUnfoldReducibleTarget___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__5;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_abstractNestedProofs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__1___closed__0;
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__1___closed__12;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Canon_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_profileitM___at___Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_inShareCommon___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_unfoldReducible_x27___lam__1___closed__0;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__8;
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markNestedSubsingletons(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__1___closed__14;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__2;
static lean_object* l_Lean_Meta_Grind_simpCore___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___redArg(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Simp_Result_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible_x27___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__1___closed__7;
static lean_object* l_Lean_Meta_Grind_simpCore___closed__0;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_normalizeLevels(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_Grind_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_pushNewFact_x27___closed__0;
static lean_object* l_Lean_Meta_Grind_preprocess___closed__1;
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_Grind_preprocess___closed__3;
static lean_object* l_Lean_Meta_Grind_preprocess___closed__6;
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(uint8_t, uint8_t);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__1___closed__5;
static lean_object* l_Lean_Meta_Grind_preprocess___closed__0;
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_simpCore___lam__1___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_inShareCommon_spec__0___redArg(x_1, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_12);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Meta_Grind_simpCore___lam__1___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpCore___lam__1___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpCore___lam__1___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_simpCore___lam__1___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpCore___lam__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpCore___lam__1___closed__6;
x_2 = l_Lean_Meta_Grind_simpCore___lam__1___closed__4;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpCore___lam__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Grind_simpCore___lam__1___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpCore___lam__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpCore___lam__1___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__13() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_simpCore___lam__1___closed__11;
x_4 = l_Lean_Meta_Grind_simpCore___lam__1___closed__12;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpCore___lam__1___closed__13;
x_2 = l_Lean_Meta_Grind_simpCore___lam__1___closed__10;
x_3 = l_Lean_Meta_Grind_simpCore___lam__1___closed__8;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_simpCore___lam__1___closed__14;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_simpCore___lam__1___closed__9;
x_4 = l_Lean_Meta_Grind_simpCore___lam__1___closed__4;
x_5 = l_Lean_Meta_Grind_simpCore___lam__1___closed__7;
x_6 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set(x_6, 4, x_2);
lean_ctor_set(x_6, 5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_14 = lean_ctor_get(x_11, 2);
x_15 = l_Lean_Meta_Grind_simpCore___lam__1___closed__15;
lean_ctor_set(x_11, 2, x_15);
x_16 = lean_st_ref_set(x_4, x_11, x_12);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_st_ref_get(x_4, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec_ref(x_18);
x_23 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_23);
lean_dec_ref(x_3);
x_24 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_24);
lean_dec_ref(x_20);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpCore___lam__0), 11, 2);
lean_closure_set(x_27, 0, x_24);
lean_closure_set(x_27, 1, x_26);
lean_ctor_set(x_21, 0, x_27);
x_28 = l_Lean_Meta_Simp_mainCore(x_1, x_23, x_14, x_21, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_st_ref_take(x_4, x_30);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_34, 2);
lean_dec(x_37);
lean_ctor_set(x_34, 2, x_32);
x_38 = lean_st_ref_set(x_4, x_34, x_35);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_31);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
x_45 = lean_ctor_get(x_34, 3);
x_46 = lean_ctor_get(x_34, 4);
x_47 = lean_ctor_get(x_34, 5);
x_48 = lean_ctor_get(x_34, 6);
x_49 = lean_ctor_get(x_34, 7);
x_50 = lean_ctor_get(x_34, 8);
x_51 = lean_ctor_get(x_34, 9);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
x_52 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_44);
lean_ctor_set(x_52, 2, x_32);
lean_ctor_set(x_52, 3, x_45);
lean_ctor_set(x_52, 4, x_46);
lean_ctor_set(x_52, 5, x_47);
lean_ctor_set(x_52, 6, x_48);
lean_ctor_set(x_52, 7, x_49);
lean_ctor_set(x_52, 8, x_50);
lean_ctor_set(x_52, 9, x_51);
x_53 = lean_st_ref_set(x_4, x_52, x_35);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_31);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_28);
if (x_57 == 0)
{
return x_28;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_28, 0);
x_59 = lean_ctor_get(x_28, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_28);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = lean_ctor_get(x_21, 0);
x_62 = lean_ctor_get(x_21, 1);
x_63 = lean_ctor_get(x_21, 2);
x_64 = lean_ctor_get(x_21, 3);
x_65 = lean_ctor_get(x_21, 4);
x_66 = lean_ctor_get_uint8(x_21, sizeof(void*)*5);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_21);
x_67 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpCore___lam__0), 11, 2);
lean_closure_set(x_67, 0, x_24);
lean_closure_set(x_67, 1, x_61);
x_68 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_62);
lean_ctor_set(x_68, 2, x_63);
lean_ctor_set(x_68, 3, x_64);
lean_ctor_set(x_68, 4, x_65);
lean_ctor_set_uint8(x_68, sizeof(void*)*5, x_66);
x_69 = l_Lean_Meta_Simp_mainCore(x_1, x_23, x_14, x_68, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_st_ref_take(x_4, x_71);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_75, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 5);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_75, 6);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_75, 7);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_75, 8);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_75, 9);
lean_inc_ref(x_85);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 lean_ctor_release(x_75, 5);
 lean_ctor_release(x_75, 6);
 lean_ctor_release(x_75, 7);
 lean_ctor_release(x_75, 8);
 lean_ctor_release(x_75, 9);
 x_86 = x_75;
} else {
 lean_dec_ref(x_75);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 10, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_77);
lean_ctor_set(x_87, 1, x_78);
lean_ctor_set(x_87, 2, x_73);
lean_ctor_set(x_87, 3, x_79);
lean_ctor_set(x_87, 4, x_80);
lean_ctor_set(x_87, 5, x_81);
lean_ctor_set(x_87, 6, x_82);
lean_ctor_set(x_87, 7, x_83);
lean_ctor_set(x_87, 8, x_84);
lean_ctor_set(x_87, 9, x_85);
x_88 = lean_st_ref_set(x_4, x_87, x_76);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_72);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_69, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_69, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_94 = x_69;
} else {
 lean_dec_ref(x_69);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_96 = lean_ctor_get(x_11, 0);
x_97 = lean_ctor_get(x_11, 1);
x_98 = lean_ctor_get(x_11, 2);
x_99 = lean_ctor_get(x_11, 3);
x_100 = lean_ctor_get(x_11, 4);
x_101 = lean_ctor_get(x_11, 5);
x_102 = lean_ctor_get(x_11, 6);
x_103 = lean_ctor_get(x_11, 7);
x_104 = lean_ctor_get(x_11, 8);
x_105 = lean_ctor_get(x_11, 9);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_11);
x_106 = l_Lean_Meta_Grind_simpCore___lam__1___closed__15;
x_107 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_107, 0, x_96);
lean_ctor_set(x_107, 1, x_97);
lean_ctor_set(x_107, 2, x_106);
lean_ctor_set(x_107, 3, x_99);
lean_ctor_set(x_107, 4, x_100);
lean_ctor_set(x_107, 5, x_101);
lean_ctor_set(x_107, 6, x_102);
lean_ctor_set(x_107, 7, x_103);
lean_ctor_set(x_107, 8, x_104);
lean_ctor_set(x_107, 9, x_105);
x_108 = lean_st_ref_set(x_4, x_107, x_12);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec_ref(x_108);
x_110 = lean_st_ref_get(x_4, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_111, 0);
lean_inc_ref(x_112);
lean_dec(x_111);
x_113 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
lean_dec_ref(x_110);
x_115 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_115);
lean_dec_ref(x_3);
x_116 = lean_ctor_get(x_112, 0);
lean_inc_ref(x_116);
lean_dec_ref(x_112);
x_117 = lean_ctor_get(x_113, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_113, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_113, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_113, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_113, 4);
lean_inc(x_121);
x_122 = lean_ctor_get_uint8(x_113, sizeof(void*)*5);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 lean_ctor_release(x_113, 4);
 x_123 = x_113;
} else {
 lean_dec_ref(x_113);
 x_123 = lean_box(0);
}
x_124 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpCore___lam__0), 11, 2);
lean_closure_set(x_124, 0, x_116);
lean_closure_set(x_124, 1, x_117);
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(0, 5, 1);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_118);
lean_ctor_set(x_125, 2, x_119);
lean_ctor_set(x_125, 3, x_120);
lean_ctor_set(x_125, 4, x_121);
lean_ctor_set_uint8(x_125, sizeof(void*)*5, x_122);
x_126 = l_Lean_Meta_Simp_mainCore(x_1, x_115, x_98, x_125, x_5, x_6, x_7, x_8, x_114);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec_ref(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_st_ref_take(x_4, x_128);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec_ref(x_131);
x_134 = lean_ctor_get(x_132, 0);
lean_inc_ref(x_134);
x_135 = lean_ctor_get(x_132, 1);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_132, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_132, 4);
lean_inc(x_137);
x_138 = lean_ctor_get(x_132, 5);
lean_inc_ref(x_138);
x_139 = lean_ctor_get(x_132, 6);
lean_inc_ref(x_139);
x_140 = lean_ctor_get(x_132, 7);
lean_inc_ref(x_140);
x_141 = lean_ctor_get(x_132, 8);
lean_inc_ref(x_141);
x_142 = lean_ctor_get(x_132, 9);
lean_inc_ref(x_142);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 lean_ctor_release(x_132, 2);
 lean_ctor_release(x_132, 3);
 lean_ctor_release(x_132, 4);
 lean_ctor_release(x_132, 5);
 lean_ctor_release(x_132, 6);
 lean_ctor_release(x_132, 7);
 lean_ctor_release(x_132, 8);
 lean_ctor_release(x_132, 9);
 x_143 = x_132;
} else {
 lean_dec_ref(x_132);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 10, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_134);
lean_ctor_set(x_144, 1, x_135);
lean_ctor_set(x_144, 2, x_130);
lean_ctor_set(x_144, 3, x_136);
lean_ctor_set(x_144, 4, x_137);
lean_ctor_set(x_144, 5, x_138);
lean_ctor_set(x_144, 6, x_139);
lean_ctor_set(x_144, 7, x_140);
lean_ctor_set(x_144, 8, x_141);
lean_ctor_set(x_144, 9, x_142);
x_145 = lean_st_ref_set(x_4, x_144, x_133);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_129);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_126, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_126, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_151 = x_126;
} else {
 lean_dec_ref(x_126);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind simp", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpCore___lam__1___boxed), 9, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Meta_Grind_simpCore___closed__0;
x_13 = lean_box(0);
x_14 = l_Lean_profileitM___at___Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg(x_12, x_10, x_11, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpCore___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpCore___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_11, 2);
x_15 = l_Lean_Meta_Grind_simpCore___lam__1___closed__15;
lean_ctor_set(x_11, 2, x_15);
x_16 = lean_st_ref_set(x_4, x_11, x_12);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_19);
lean_dec_ref(x_3);
x_20 = l_Lean_Meta_Simp_dsimpMainCore(x_1, x_18, x_14, x_19, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_st_ref_take(x_4, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_26, 2);
lean_dec(x_29);
lean_ctor_set(x_26, 2, x_24);
x_30 = lean_st_ref_set(x_4, x_26, x_27);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_23);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
x_37 = lean_ctor_get(x_26, 3);
x_38 = lean_ctor_get(x_26, 4);
x_39 = lean_ctor_get(x_26, 5);
x_40 = lean_ctor_get(x_26, 6);
x_41 = lean_ctor_get(x_26, 7);
x_42 = lean_ctor_get(x_26, 8);
x_43 = lean_ctor_get(x_26, 9);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_44 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_24);
lean_ctor_set(x_44, 3, x_37);
lean_ctor_set(x_44, 4, x_38);
lean_ctor_set(x_44, 5, x_39);
lean_ctor_set(x_44, 6, x_40);
lean_ctor_set(x_44, 7, x_41);
lean_ctor_set(x_44, 8, x_42);
lean_ctor_set(x_44, 9, x_43);
x_45 = lean_st_ref_set(x_4, x_44, x_27);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_23);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_20);
if (x_49 == 0)
{
return x_20;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_20, 0);
x_51 = lean_ctor_get(x_20, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_20);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_53 = lean_ctor_get(x_11, 0);
x_54 = lean_ctor_get(x_11, 1);
x_55 = lean_ctor_get(x_11, 2);
x_56 = lean_ctor_get(x_11, 3);
x_57 = lean_ctor_get(x_11, 4);
x_58 = lean_ctor_get(x_11, 5);
x_59 = lean_ctor_get(x_11, 6);
x_60 = lean_ctor_get(x_11, 7);
x_61 = lean_ctor_get(x_11, 8);
x_62 = lean_ctor_get(x_11, 9);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_11);
x_63 = l_Lean_Meta_Grind_simpCore___lam__1___closed__15;
x_64 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_54);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_64, 3, x_56);
lean_ctor_set(x_64, 4, x_57);
lean_ctor_set(x_64, 5, x_58);
lean_ctor_set(x_64, 6, x_59);
lean_ctor_set(x_64, 7, x_60);
lean_ctor_set(x_64, 8, x_61);
lean_ctor_set(x_64, 9, x_62);
x_65 = lean_st_ref_set(x_4, x_64, x_12);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_68);
lean_dec_ref(x_3);
x_69 = l_Lean_Meta_Simp_dsimpMainCore(x_1, x_67, x_55, x_68, x_5, x_6, x_7, x_8, x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_st_ref_take(x_4, x_71);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_75, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 5);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_75, 6);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_75, 7);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_75, 8);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_75, 9);
lean_inc_ref(x_85);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 lean_ctor_release(x_75, 5);
 lean_ctor_release(x_75, 6);
 lean_ctor_release(x_75, 7);
 lean_ctor_release(x_75, 8);
 lean_ctor_release(x_75, 9);
 x_86 = x_75;
} else {
 lean_dec_ref(x_75);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 10, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_77);
lean_ctor_set(x_87, 1, x_78);
lean_ctor_set(x_87, 2, x_73);
lean_ctor_set(x_87, 3, x_79);
lean_ctor_set(x_87, 4, x_80);
lean_ctor_set(x_87, 5, x_81);
lean_ctor_set(x_87, 6, x_82);
lean_ctor_set(x_87, 7, x_83);
lean_ctor_set(x_87, 8, x_84);
lean_ctor_set(x_87, 9, x_85);
x_88 = lean_st_ref_set(x_4, x_87, x_76);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_72);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_69, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_69, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_94 = x_69;
} else {
 lean_dec_ref(x_69);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_dsimpCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind dsimp", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_dsimpCore___lam__0___boxed), 9, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Meta_Grind_dsimpCore___closed__0;
x_13 = lean_box(0);
x_14 = l_Lean_profileitM___at___Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg(x_12, x_10, x_11, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_dsimpCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_dsimpCore___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = lean_get_reducibility_status(x_7, x_1);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_12);
lean_dec(x_10);
x_13 = lean_get_reducibility_status(x_12, x_1);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_getReducibilityStatus___at___Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0_spec__0___redArg(x_1, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_getReducibilityStatus___at___Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0_spec__0___redArg(x_1, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = 1;
x_15 = lean_box(x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = 1;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_11);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
lean_dec(x_21);
x_22 = 0;
x_23 = lean_box(x_22);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_4, x_3);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_uget(x_5, x_4);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_2, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_uset(x_5, x_4, x_21);
x_23 = 1;
x_24 = lean_usize_add(x_4, x_23);
x_25 = lean_array_uset(x_22, x_4, x_19);
x_4 = x_24;
x_5 = x_25;
x_14 = x_20;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_3);
x_13 = lean_apply_9(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
switch (lean_obj_tag(x_14)) {
case 0:
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_17);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
case 1:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_3);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec_ref(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_22);
lean_dec(x_14);
x_23 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_2, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
return x_23;
}
default: 
{
lean_object* x_24; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_13, 0);
lean_dec(x_26);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec_ref(x_3);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_13, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_24, 0);
lean_inc(x_31);
lean_dec(x_24);
lean_ctor_set(x_13, 0, x_31);
return x_13;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_dec(x_13);
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_3);
x_17 = lean_array_set(x_4, x_5, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_5, x_18);
lean_dec(x_5);
x_3 = x_15;
x_4 = x_17;
x_5 = x_19;
goto _start;
}
else
{
lean_object* x_21; 
lean_dec(x_5);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_array_size(x_4);
x_25 = 0;
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_26 = l_Array_mapMUnsafe_map___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__2(x_1, x_2, x_24, x_25, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l_Lean_mkAppN(x_22, x_27);
lean_dec(x_27);
x_30 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_2, x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_28);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_22);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_3);
x_17 = lean_array_set(x_4, x_5, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_5, x_18);
x_20 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__4_spec__4(x_1, x_2, x_15, x_17, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_20;
}
else
{
lean_object* x_21; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_array_size(x_4);
x_25 = 0;
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_26 = l_Array_mapMUnsafe_map___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__2(x_1, x_2, x_24, x_25, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l_Lean_mkAppN(x_22, x_27);
lean_dec(x_27);
x_30 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_2, x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_28);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_22);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_17; 
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 3);
x_22 = lean_ctor_get(x_8, 4);
x_23 = lean_ctor_get(x_8, 5);
x_24 = lean_ctor_get(x_8, 6);
x_25 = lean_ctor_get(x_8, 7);
x_26 = lean_ctor_get(x_8, 8);
x_27 = lean_ctor_get(x_8, 9);
x_28 = lean_ctor_get(x_8, 10);
x_29 = lean_ctor_get(x_8, 11);
x_30 = lean_ctor_get(x_8, 12);
x_31 = lean_nat_dec_eq(x_21, x_22);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_21, x_32);
lean_dec(x_21);
lean_ctor_set(x_8, 3, x_33);
x_34 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_11 = x_34;
goto block_16;
}
else
{
lean_object* x_35; 
lean_free_object(x_8);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4_spec__4___redArg(x_23, x_10);
x_11 = x_35;
goto block_16;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; 
x_36 = lean_ctor_get(x_8, 0);
x_37 = lean_ctor_get(x_8, 1);
x_38 = lean_ctor_get(x_8, 2);
x_39 = lean_ctor_get(x_8, 3);
x_40 = lean_ctor_get(x_8, 4);
x_41 = lean_ctor_get(x_8, 5);
x_42 = lean_ctor_get(x_8, 6);
x_43 = lean_ctor_get(x_8, 7);
x_44 = lean_ctor_get(x_8, 8);
x_45 = lean_ctor_get(x_8, 9);
x_46 = lean_ctor_get(x_8, 10);
x_47 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_48 = lean_ctor_get(x_8, 11);
x_49 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_50 = lean_ctor_get(x_8, 12);
lean_inc(x_50);
lean_inc(x_48);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_8);
x_51 = lean_nat_dec_eq(x_39, x_40);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_39, x_52);
lean_dec(x_39);
x_54 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_54, 0, x_36);
lean_ctor_set(x_54, 1, x_37);
lean_ctor_set(x_54, 2, x_38);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_40);
lean_ctor_set(x_54, 5, x_41);
lean_ctor_set(x_54, 6, x_42);
lean_ctor_set(x_54, 7, x_43);
lean_ctor_set(x_54, 8, x_44);
lean_ctor_set(x_54, 9, x_45);
lean_ctor_set(x_54, 10, x_46);
lean_ctor_set(x_54, 11, x_48);
lean_ctor_set(x_54, 12, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*13, x_47);
lean_ctor_set_uint8(x_54, sizeof(void*)*13 + 1, x_49);
x_55 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_54, x_9, x_10);
x_11 = x_55;
goto block_16;
}
else
{
lean_object* x_56; 
lean_dec_ref(x_50);
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4_spec__4___redArg(x_41, x_10);
x_11 = x_56;
goto block_16;
}
}
block_16:
{
if (lean_obj_tag(x_11) == 0)
{
return x_11;
}
else
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
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Core_withIncRecDepth___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__6___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_apply_1(x_2, x_10);
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
}
static lean_object* _init_l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_59; 
lean_inc(x_1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_59 = lean_apply_9(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
switch (lean_obj_tag(x_61)) {
case 0:
{
lean_object* x_147; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_147 = lean_ctor_get(x_61, 0);
lean_inc_ref(x_147);
lean_dec(x_61);
lean_ctor_set(x_59, 0, x_147);
return x_59;
}
case 1:
{
lean_object* x_148; lean_object* x_149; 
lean_free_object(x_59);
lean_dec_ref(x_2);
x_148 = lean_ctor_get(x_61, 0);
lean_inc_ref(x_148);
lean_dec(x_61);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_149 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_148, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_62);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec_ref(x_149);
x_152 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_150, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_151);
return x_152;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_149;
}
}
default: 
{
lean_object* x_153; 
lean_free_object(x_59);
x_153 = lean_ctor_get(x_61, 0);
lean_inc(x_153);
lean_dec(x_61);
if (lean_obj_tag(x_153) == 0)
{
x_63 = x_2;
goto block_146;
}
else
{
lean_object* x_154; 
lean_dec_ref(x_2);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec(x_153);
x_63 = x_154;
goto block_146;
}
}
}
block_146:
{
switch (lean_obj_tag(x_63)) {
case 5:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__1___closed__0;
x_65 = l_Lean_Expr_getAppNumArgs(x_63);
lean_inc(x_65);
x_66 = lean_mk_array(x_65, x_64);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_sub(x_65, x_67);
lean_dec(x_65);
x_69 = l_Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__4(x_1, x_3, x_63, x_66, x_68, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_62);
lean_dec(x_68);
return x_69;
}
case 6:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_63, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_63, 1);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_63, 2);
lean_inc_ref(x_72);
x_73 = lean_ctor_get_uint8(x_63, sizeof(void*)*3 + 8);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_71);
lean_inc(x_3);
lean_inc(x_1);
x_74 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_71, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_62);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_72);
lean_inc(x_3);
lean_inc(x_1);
x_77 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_72, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; size_t x_80; size_t x_81; uint8_t x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = lean_ptr_addr(x_71);
lean_dec_ref(x_71);
x_81 = lean_ptr_addr(x_75);
x_82 = lean_usize_dec_eq(x_80, x_81);
if (x_82 == 0)
{
lean_dec_ref(x_72);
x_45 = x_79;
x_46 = x_75;
x_47 = x_78;
x_48 = x_73;
x_49 = x_70;
x_50 = x_63;
x_51 = x_82;
goto block_58;
}
else
{
size_t x_83; size_t x_84; uint8_t x_85; 
x_83 = lean_ptr_addr(x_72);
lean_dec_ref(x_72);
x_84 = lean_ptr_addr(x_78);
x_85 = lean_usize_dec_eq(x_83, x_84);
x_45 = x_79;
x_46 = x_75;
x_47 = x_78;
x_48 = x_73;
x_49 = x_70;
x_50 = x_63;
x_51 = x_85;
goto block_58;
}
}
else
{
lean_dec(x_75);
lean_dec_ref(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_63);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_77;
}
}
else
{
lean_dec_ref(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_63);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_74;
}
}
case 7:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_63, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_63, 1);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_63, 2);
lean_inc_ref(x_88);
x_89 = lean_ctor_get_uint8(x_63, sizeof(void*)*3 + 8);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_87);
lean_inc(x_3);
lean_inc(x_1);
x_90 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_87, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_62);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec_ref(x_90);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_88);
lean_inc(x_3);
lean_inc(x_1);
x_93 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_88, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; size_t x_96; size_t x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec_ref(x_93);
x_96 = lean_ptr_addr(x_87);
lean_dec_ref(x_87);
x_97 = lean_ptr_addr(x_91);
x_98 = lean_usize_dec_eq(x_96, x_97);
if (x_98 == 0)
{
lean_dec_ref(x_88);
x_31 = x_95;
x_32 = x_94;
x_33 = x_86;
x_34 = x_91;
x_35 = x_89;
x_36 = x_63;
x_37 = x_98;
goto block_44;
}
else
{
size_t x_99; size_t x_100; uint8_t x_101; 
x_99 = lean_ptr_addr(x_88);
lean_dec_ref(x_88);
x_100 = lean_ptr_addr(x_94);
x_101 = lean_usize_dec_eq(x_99, x_100);
x_31 = x_95;
x_32 = x_94;
x_33 = x_86;
x_34 = x_91;
x_35 = x_89;
x_36 = x_63;
x_37 = x_101;
goto block_44;
}
}
else
{
lean_dec(x_91);
lean_dec_ref(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec_ref(x_63);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_93;
}
}
else
{
lean_dec_ref(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec_ref(x_63);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_90;
}
}
case 8:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_63, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_63, 1);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_63, 2);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_63, 3);
lean_inc_ref(x_105);
x_106 = lean_ctor_get_uint8(x_63, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_103);
lean_inc(x_3);
lean_inc(x_1);
x_107 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_103, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_62);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec_ref(x_107);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_104);
lean_inc(x_3);
lean_inc(x_1);
x_110 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_104, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec_ref(x_110);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_105);
lean_inc(x_3);
lean_inc(x_1);
x_113 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_105, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; size_t x_116; size_t x_117; uint8_t x_118; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec_ref(x_113);
x_116 = lean_ptr_addr(x_103);
lean_dec_ref(x_103);
x_117 = lean_ptr_addr(x_108);
x_118 = lean_usize_dec_eq(x_116, x_117);
if (x_118 == 0)
{
lean_dec_ref(x_104);
x_13 = x_105;
x_14 = x_102;
x_15 = x_114;
x_16 = x_111;
x_17 = x_106;
x_18 = x_108;
x_19 = x_63;
x_20 = x_115;
x_21 = x_118;
goto block_30;
}
else
{
size_t x_119; size_t x_120; uint8_t x_121; 
x_119 = lean_ptr_addr(x_104);
lean_dec_ref(x_104);
x_120 = lean_ptr_addr(x_111);
x_121 = lean_usize_dec_eq(x_119, x_120);
x_13 = x_105;
x_14 = x_102;
x_15 = x_114;
x_16 = x_111;
x_17 = x_106;
x_18 = x_108;
x_19 = x_63;
x_20 = x_115;
x_21 = x_121;
goto block_30;
}
}
else
{
lean_dec(x_111);
lean_dec(x_108);
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_63);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_113;
}
}
else
{
lean_dec(x_108);
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_63);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_110;
}
}
else
{
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_63);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_107;
}
}
case 10:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_63, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_63, 1);
lean_inc_ref(x_123);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_123);
lean_inc(x_3);
lean_inc(x_1);
x_124 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_123, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_62);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; size_t x_127; size_t x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec_ref(x_124);
x_127 = lean_ptr_addr(x_123);
lean_dec_ref(x_123);
x_128 = lean_ptr_addr(x_125);
x_129 = lean_usize_dec_eq(x_127, x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec_ref(x_63);
x_130 = l_Lean_Expr_mdata___override(x_122, x_125);
x_131 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_130, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_126);
return x_131;
}
else
{
lean_object* x_132; 
lean_dec(x_125);
lean_dec(x_122);
x_132 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_63, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_126);
return x_132;
}
}
else
{
lean_dec_ref(x_123);
lean_dec(x_122);
lean_dec_ref(x_63);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_124;
}
}
case 11:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_63, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_63, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_63, 2);
lean_inc_ref(x_135);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_135);
lean_inc(x_3);
lean_inc(x_1);
x_136 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_135, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_62);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; size_t x_139; size_t x_140; uint8_t x_141; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec_ref(x_136);
x_139 = lean_ptr_addr(x_135);
lean_dec_ref(x_135);
x_140 = lean_ptr_addr(x_137);
x_141 = lean_usize_dec_eq(x_139, x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
lean_dec_ref(x_63);
x_142 = l_Lean_Expr_proj___override(x_133, x_134, x_137);
x_143 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_142, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_138);
return x_143;
}
else
{
lean_object* x_144; 
lean_dec(x_137);
lean_dec(x_134);
lean_dec(x_133);
x_144 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_63, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_138);
return x_144;
}
}
else
{
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_63);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_136;
}
}
default: 
{
lean_object* x_145; 
x_145 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_63, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_62);
return x_145;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_59, 0);
x_156 = lean_ctor_get(x_59, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_59);
switch (lean_obj_tag(x_155)) {
case 0:
{
lean_object* x_241; lean_object* x_242; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_241 = lean_ctor_get(x_155, 0);
lean_inc_ref(x_241);
lean_dec(x_155);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_156);
return x_242;
}
case 1:
{
lean_object* x_243; lean_object* x_244; 
lean_dec_ref(x_2);
x_243 = lean_ctor_get(x_155, 0);
lean_inc_ref(x_243);
lean_dec(x_155);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_244 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_243, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_156);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec_ref(x_244);
x_247 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_245, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_246);
return x_247;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_244;
}
}
default: 
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_155, 0);
lean_inc(x_248);
lean_dec(x_155);
if (lean_obj_tag(x_248) == 0)
{
x_157 = x_2;
goto block_240;
}
else
{
lean_object* x_249; 
lean_dec_ref(x_2);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
lean_dec(x_248);
x_157 = x_249;
goto block_240;
}
}
}
block_240:
{
switch (lean_obj_tag(x_157)) {
case 5:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_158 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__1___closed__0;
x_159 = l_Lean_Expr_getAppNumArgs(x_157);
lean_inc(x_159);
x_160 = lean_mk_array(x_159, x_158);
x_161 = lean_unsigned_to_nat(1u);
x_162 = lean_nat_sub(x_159, x_161);
lean_dec(x_159);
x_163 = l_Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__4(x_1, x_3, x_157, x_160, x_162, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_156);
lean_dec(x_162);
return x_163;
}
case 6:
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; 
x_164 = lean_ctor_get(x_157, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_157, 1);
lean_inc_ref(x_165);
x_166 = lean_ctor_get(x_157, 2);
lean_inc_ref(x_166);
x_167 = lean_ctor_get_uint8(x_157, sizeof(void*)*3 + 8);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_165);
lean_inc(x_3);
lean_inc(x_1);
x_168 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_165, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_156);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec_ref(x_168);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_166);
lean_inc(x_3);
lean_inc(x_1);
x_171 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_166, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; size_t x_174; size_t x_175; uint8_t x_176; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec_ref(x_171);
x_174 = lean_ptr_addr(x_165);
lean_dec_ref(x_165);
x_175 = lean_ptr_addr(x_169);
x_176 = lean_usize_dec_eq(x_174, x_175);
if (x_176 == 0)
{
lean_dec_ref(x_166);
x_45 = x_173;
x_46 = x_169;
x_47 = x_172;
x_48 = x_167;
x_49 = x_164;
x_50 = x_157;
x_51 = x_176;
goto block_58;
}
else
{
size_t x_177; size_t x_178; uint8_t x_179; 
x_177 = lean_ptr_addr(x_166);
lean_dec_ref(x_166);
x_178 = lean_ptr_addr(x_172);
x_179 = lean_usize_dec_eq(x_177, x_178);
x_45 = x_173;
x_46 = x_169;
x_47 = x_172;
x_48 = x_167;
x_49 = x_164;
x_50 = x_157;
x_51 = x_179;
goto block_58;
}
}
else
{
lean_dec(x_169);
lean_dec_ref(x_166);
lean_dec_ref(x_165);
lean_dec(x_164);
lean_dec_ref(x_157);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_171;
}
}
else
{
lean_dec_ref(x_166);
lean_dec_ref(x_165);
lean_dec(x_164);
lean_dec_ref(x_157);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_168;
}
}
case 7:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; 
x_180 = lean_ctor_get(x_157, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_157, 1);
lean_inc_ref(x_181);
x_182 = lean_ctor_get(x_157, 2);
lean_inc_ref(x_182);
x_183 = lean_ctor_get_uint8(x_157, sizeof(void*)*3 + 8);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_181);
lean_inc(x_3);
lean_inc(x_1);
x_184 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_181, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_156);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec_ref(x_184);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_182);
lean_inc(x_3);
lean_inc(x_1);
x_187 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_182, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_186);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; size_t x_190; size_t x_191; uint8_t x_192; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec_ref(x_187);
x_190 = lean_ptr_addr(x_181);
lean_dec_ref(x_181);
x_191 = lean_ptr_addr(x_185);
x_192 = lean_usize_dec_eq(x_190, x_191);
if (x_192 == 0)
{
lean_dec_ref(x_182);
x_31 = x_189;
x_32 = x_188;
x_33 = x_180;
x_34 = x_185;
x_35 = x_183;
x_36 = x_157;
x_37 = x_192;
goto block_44;
}
else
{
size_t x_193; size_t x_194; uint8_t x_195; 
x_193 = lean_ptr_addr(x_182);
lean_dec_ref(x_182);
x_194 = lean_ptr_addr(x_188);
x_195 = lean_usize_dec_eq(x_193, x_194);
x_31 = x_189;
x_32 = x_188;
x_33 = x_180;
x_34 = x_185;
x_35 = x_183;
x_36 = x_157;
x_37 = x_195;
goto block_44;
}
}
else
{
lean_dec(x_185);
lean_dec_ref(x_182);
lean_dec_ref(x_181);
lean_dec(x_180);
lean_dec_ref(x_157);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_187;
}
}
else
{
lean_dec_ref(x_182);
lean_dec_ref(x_181);
lean_dec(x_180);
lean_dec_ref(x_157);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_184;
}
}
case 8:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; 
x_196 = lean_ctor_get(x_157, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_157, 1);
lean_inc_ref(x_197);
x_198 = lean_ctor_get(x_157, 2);
lean_inc_ref(x_198);
x_199 = lean_ctor_get(x_157, 3);
lean_inc_ref(x_199);
x_200 = lean_ctor_get_uint8(x_157, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_197);
lean_inc(x_3);
lean_inc(x_1);
x_201 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_197, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_156);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec_ref(x_201);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_198);
lean_inc(x_3);
lean_inc(x_1);
x_204 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_198, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec_ref(x_204);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_199);
lean_inc(x_3);
lean_inc(x_1);
x_207 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_199, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; size_t x_210; size_t x_211; uint8_t x_212; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec_ref(x_207);
x_210 = lean_ptr_addr(x_197);
lean_dec_ref(x_197);
x_211 = lean_ptr_addr(x_202);
x_212 = lean_usize_dec_eq(x_210, x_211);
if (x_212 == 0)
{
lean_dec_ref(x_198);
x_13 = x_199;
x_14 = x_196;
x_15 = x_208;
x_16 = x_205;
x_17 = x_200;
x_18 = x_202;
x_19 = x_157;
x_20 = x_209;
x_21 = x_212;
goto block_30;
}
else
{
size_t x_213; size_t x_214; uint8_t x_215; 
x_213 = lean_ptr_addr(x_198);
lean_dec_ref(x_198);
x_214 = lean_ptr_addr(x_205);
x_215 = lean_usize_dec_eq(x_213, x_214);
x_13 = x_199;
x_14 = x_196;
x_15 = x_208;
x_16 = x_205;
x_17 = x_200;
x_18 = x_202;
x_19 = x_157;
x_20 = x_209;
x_21 = x_215;
goto block_30;
}
}
else
{
lean_dec(x_205);
lean_dec(x_202);
lean_dec_ref(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_196);
lean_dec_ref(x_157);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_207;
}
}
else
{
lean_dec(x_202);
lean_dec_ref(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_196);
lean_dec_ref(x_157);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_204;
}
}
else
{
lean_dec_ref(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_197);
lean_dec(x_196);
lean_dec_ref(x_157);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_201;
}
}
case 10:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_157, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_157, 1);
lean_inc_ref(x_217);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_217);
lean_inc(x_3);
lean_inc(x_1);
x_218 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_217, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_156);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; size_t x_221; size_t x_222; uint8_t x_223; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec_ref(x_218);
x_221 = lean_ptr_addr(x_217);
lean_dec_ref(x_217);
x_222 = lean_ptr_addr(x_219);
x_223 = lean_usize_dec_eq(x_221, x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; 
lean_dec_ref(x_157);
x_224 = l_Lean_Expr_mdata___override(x_216, x_219);
x_225 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_224, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_220);
return x_225;
}
else
{
lean_object* x_226; 
lean_dec(x_219);
lean_dec(x_216);
x_226 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_157, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_220);
return x_226;
}
}
else
{
lean_dec_ref(x_217);
lean_dec(x_216);
lean_dec_ref(x_157);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_218;
}
}
case 11:
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_227 = lean_ctor_get(x_157, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_157, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_157, 2);
lean_inc_ref(x_229);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_229);
lean_inc(x_3);
lean_inc(x_1);
x_230 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_1, x_3, x_229, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_156);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; size_t x_233; size_t x_234; uint8_t x_235; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec_ref(x_230);
x_233 = lean_ptr_addr(x_229);
lean_dec_ref(x_229);
x_234 = lean_ptr_addr(x_231);
x_235 = lean_usize_dec_eq(x_233, x_234);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; 
lean_dec_ref(x_157);
x_236 = l_Lean_Expr_proj___override(x_227, x_228, x_231);
x_237 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_236, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_232);
return x_237;
}
else
{
lean_object* x_238; 
lean_dec(x_231);
lean_dec(x_228);
lean_dec(x_227);
x_238 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_157, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_232);
return x_238;
}
}
else
{
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec_ref(x_157);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_230;
}
}
default: 
{
lean_object* x_239; 
x_239 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_157, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_156);
return x_239;
}
}
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_250 = !lean_is_exclusive(x_59);
if (x_250 == 0)
{
return x_59;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_59, 0);
x_252 = lean_ctor_get(x_59, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_59);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
block_30:
{
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_22 = l_Lean_Expr_letE___override(x_14, x_18, x_16, x_15, x_17);
x_23 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
return x_23;
}
else
{
size_t x_24; size_t x_25; uint8_t x_26; 
x_24 = lean_ptr_addr(x_13);
lean_dec_ref(x_13);
x_25 = lean_ptr_addr(x_15);
x_26 = lean_usize_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_19);
x_27 = l_Lean_Expr_letE___override(x_14, x_18, x_16, x_15, x_17);
x_28 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec_ref(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
x_29 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
return x_29;
}
}
}
block_44:
{
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_36);
x_38 = l_Lean_Expr_forallE___override(x_33, x_34, x_32, x_35);
x_39 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_35, x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_36);
x_41 = l_Lean_Expr_forallE___override(x_33, x_34, x_32, x_35);
x_42 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_41, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
return x_42;
}
else
{
lean_object* x_43; 
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
x_43 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_36, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
return x_43;
}
}
}
block_58:
{
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_50);
x_52 = l_Lean_Expr_lam___override(x_49, x_46, x_47, x_48);
x_53 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_52, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
return x_53;
}
else
{
uint8_t x_54; 
x_54 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_48, x_48);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec_ref(x_50);
x_55 = l_Lean_Expr_lam___override(x_49, x_46, x_47, x_48);
x_56 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
return x_56;
}
else
{
lean_object* x_57; 
lean_dec(x_49);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
x_57 = l_Lean_Core_transform_visit_visitPost___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__3(x_1, x_3, x_50, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_box(0);
x_21 = lean_array_get_size(x_12);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = lean_usize_sub(x_22, x_2);
x_24 = lean_usize_land(x_3, x_23);
x_25 = lean_array_uget(x_12, x_24);
x_26 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___redArg(x_4, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_11, x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_5);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_12, x_24, x_29);
x_31 = lean_unsigned_to_nat(4u);
x_32 = lean_nat_mul(x_28, x_31);
x_33 = lean_unsigned_to_nat(3u);
x_34 = lean_nat_div(x_32, x_33);
lean_dec(x_32);
x_35 = lean_array_get_size(x_30);
x_36 = lean_nat_dec_le(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2___redArg(x_30);
lean_ctor_set(x_8, 1, x_37);
lean_ctor_set(x_8, 0, x_28);
x_14 = x_8;
goto block_20;
}
else
{
lean_ctor_set(x_8, 1, x_30);
lean_ctor_set(x_8, 0, x_28);
x_14 = x_8;
goto block_20;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_box(0);
x_39 = lean_array_uset(x_12, x_24, x_38);
x_40 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5___redArg(x_4, x_5, x_25);
x_41 = lean_array_uset(x_39, x_24, x_40);
lean_ctor_set(x_8, 1, x_41);
x_14 = x_8;
goto block_20;
}
block_20:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_st_ref_set(x_1, x_14, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_13);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_51; size_t x_52; size_t x_53; size_t x_54; lean_object* x_55; uint8_t x_56; 
x_42 = lean_ctor_get(x_8, 0);
x_43 = lean_ctor_get(x_8, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_8);
x_44 = lean_box(0);
x_51 = lean_array_get_size(x_43);
x_52 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_53 = lean_usize_sub(x_52, x_2);
x_54 = lean_usize_land(x_3, x_53);
x_55 = lean_array_uget(x_43, x_54);
x_56 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1___redArg(x_4, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_42, x_57);
lean_dec(x_42);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_4);
lean_ctor_set(x_59, 1, x_5);
lean_ctor_set(x_59, 2, x_55);
x_60 = lean_array_uset(x_43, x_54, x_59);
x_61 = lean_unsigned_to_nat(4u);
x_62 = lean_nat_mul(x_58, x_61);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_nat_div(x_62, x_63);
lean_dec(x_62);
x_65 = lean_array_get_size(x_60);
x_66 = lean_nat_dec_le(x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2___redArg(x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_67);
x_45 = x_68;
goto block_50;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_60);
x_45 = x_69;
goto block_50;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_box(0);
x_71 = lean_array_uset(x_43, x_54, x_70);
x_72 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5___redArg(x_4, x_5, x_55);
x_73 = lean_array_uset(x_71, x_54, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_42);
lean_ctor_set(x_74, 1, x_73);
x_45 = x_74;
goto block_50;
}
block_50:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_st_ref_set(x_1, x_45, x_9);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
static lean_object* _init_l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_4);
x_13 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, lean_box(0));
lean_closure_set(x_13, 2, x_4);
x_14 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__0(lean_box(0), x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_18);
lean_dec(x_16);
x_19 = lean_array_get_size(x_18);
x_20 = l_Lean_Expr_hash(x_3);
x_21 = 32;
x_22 = lean_uint64_shift_right(x_20, x_21);
x_23 = lean_uint64_xor(x_20, x_22);
x_24 = 16;
x_25 = lean_uint64_shift_right(x_23, x_24);
x_26 = lean_uint64_xor(x_23, x_25);
x_27 = lean_uint64_to_usize(x_26);
x_28 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_29 = 1;
x_30 = lean_usize_sub(x_28, x_29);
x_31 = lean_usize_land(x_27, x_30);
x_32 = lean_array_uget(x_18, x_31);
lean_dec_ref(x_18);
x_33 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0___redArg(x_3, x_32);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_free_object(x_14);
lean_inc_ref(x_3);
x_34 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__1), 12, 3);
lean_closure_set(x_34, 0, x_1);
lean_closure_set(x_34, 1, x_3);
lean_closure_set(x_34, 2, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_35 = l_Lean_Core_withIncRecDepth___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__6___redArg(x_34, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___boxed__const__1;
x_39 = lean_box_usize(x_27);
lean_inc(x_36);
x_40 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__2___boxed), 6, 5);
lean_closure_set(x_40, 0, x_4);
lean_closure_set(x_40, 1, x_38);
lean_closure_set(x_40, 2, x_39);
lean_closure_set(x_40, 3, x_3);
lean_closure_set(x_40, 4, x_36);
x_41 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__0(lean_box(0), x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_37);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_36);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_35;
}
}
else
{
lean_object* x_46; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_ctor_get(x_33, 0);
lean_inc(x_46);
lean_dec(x_33);
lean_ctor_set(x_14, 0, x_46);
return x_14;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; size_t x_58; size_t x_59; size_t x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; 
x_47 = lean_ctor_get(x_14, 0);
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_14);
x_49 = lean_ctor_get(x_47, 1);
lean_inc_ref(x_49);
lean_dec(x_47);
x_50 = lean_array_get_size(x_49);
x_51 = l_Lean_Expr_hash(x_3);
x_52 = 32;
x_53 = lean_uint64_shift_right(x_51, x_52);
x_54 = lean_uint64_xor(x_51, x_53);
x_55 = 16;
x_56 = lean_uint64_shift_right(x_54, x_55);
x_57 = lean_uint64_xor(x_54, x_56);
x_58 = lean_uint64_to_usize(x_57);
x_59 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_60 = 1;
x_61 = lean_usize_sub(x_59, x_60);
x_62 = lean_usize_land(x_58, x_61);
x_63 = lean_array_uget(x_49, x_62);
lean_dec_ref(x_49);
x_64 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0___redArg(x_3, x_63);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_inc_ref(x_3);
x_65 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__1), 12, 3);
lean_closure_set(x_65, 0, x_1);
lean_closure_set(x_65, 1, x_3);
lean_closure_set(x_65, 2, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_66 = l_Lean_Core_withIncRecDepth___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__6___redArg(x_65, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_48);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec_ref(x_66);
x_69 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___boxed__const__1;
x_70 = lean_box_usize(x_58);
lean_inc(x_67);
x_71 = lean_alloc_closure((void*)(l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__2___boxed), 6, 5);
lean_closure_set(x_71, 0, x_4);
lean_closure_set(x_71, 1, x_69);
lean_closure_set(x_71, 2, x_70);
lean_closure_set(x_71, 3, x_3);
lean_closure_set(x_71, 4, x_67);
x_72 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__0(lean_box(0), x_71, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_68);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_66;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = lean_ctor_get(x_64, 0);
lean_inc(x_76);
lean_dec(x_64);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_48);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_apply_1(x_2, x_10);
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
}
static lean_object* _init_l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpCore___lam__1___closed__4;
x_2 = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2___closed__0;
x_13 = l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2___lam__0(lean_box(0), x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_16 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2(x_2, x_3, x_1, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_19, 0, lean_box(0));
lean_closure_set(x_19, 1, lean_box(0));
lean_closure_set(x_19, 2, x_14);
x_20 = l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2___lam__0(lean_box(0), x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_17);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible_x27___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Grind_unfoldReducible_x27___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible_x27___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_Grind_inShareCommon___redArg(x_1, x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_free_object(x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_17);
x_18 = l_Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = l_Lean_Meta_Grind_unfoldReducible_x27___lam__1___closed__0;
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = l_Lean_Meta_Grind_unfoldReducible_x27___lam__1___closed__0;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_18, 1);
x_29 = lean_ctor_get(x_18, 0);
lean_dec(x_29);
x_30 = l_Lean_Meta_Grind_isGrindGadget(x_17);
lean_dec(x_17);
if (x_30 == 0)
{
lean_object* x_31; 
lean_free_object(x_18);
x_31 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_30, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
return x_31;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_31, 0, x_43);
return x_31;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_31, 1);
lean_inc(x_44);
lean_dec(x_31);
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_46 = x_32;
} else {
 lean_dec_ref(x_32);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_31);
if (x_49 == 0)
{
return x_31;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_31, 0);
x_51 = lean_ctor_get(x_31, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_31);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_53 = l_Lean_Meta_Grind_unfoldReducible_x27___lam__1___closed__0;
lean_ctor_set(x_18, 0, x_53);
return x_18;
}
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_18, 1);
lean_inc(x_54);
lean_dec(x_18);
x_55 = l_Lean_Meta_Grind_isGrindGadget(x_17);
lean_dec(x_17);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_55, x_5, x_6, x_7, x_8, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_57);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_63 = x_56;
} else {
 lean_dec_ref(x_56);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_57, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_65 = x_57;
} else {
 lean_dec_ref(x_57);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_64);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_56, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_56, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_70 = x_56;
} else {
 lean_dec_ref(x_56);
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
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_72 = l_Lean_Meta_Grind_unfoldReducible_x27___lam__1___closed__0;
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_54);
return x_73;
}
}
}
}
else
{
lean_object* x_74; 
lean_dec_ref(x_16);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_74 = l_Lean_Meta_Grind_unfoldReducible_x27___lam__1___closed__0;
lean_ctor_set(x_10, 0, x_74);
return x_10;
}
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_10, 1);
lean_inc(x_75);
lean_dec(x_10);
x_76 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_76) == 4)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
lean_inc(x_77);
x_78 = l_Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0(x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_75);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_77);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_82 = x_78;
} else {
 lean_dec_ref(x_78);
 x_82 = lean_box(0);
}
x_83 = l_Lean_Meta_Grind_unfoldReducible_x27___lam__1___closed__0;
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_86 = x_78;
} else {
 lean_dec_ref(x_78);
 x_86 = lean_box(0);
}
x_87 = l_Lean_Meta_Grind_isGrindGadget(x_77);
lean_dec(x_77);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_86);
x_88 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_87, x_5, x_6, x_7, x_8, x_85);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
x_92 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_92, 0, x_89);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_95 = x_88;
} else {
 lean_dec_ref(x_88);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_89, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_97 = x_89;
} else {
 lean_dec_ref(x_89);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_96);
if (lean_is_scalar(x_95)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_95;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_94);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_88, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_88, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_102 = x_88;
} else {
 lean_dec_ref(x_88);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_104 = l_Lean_Meta_Grind_unfoldReducible_x27___lam__1___closed__0;
if (lean_is_scalar(x_86)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_86;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_85);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec_ref(x_76);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_106 = l_Lean_Meta_Grind_unfoldReducible_x27___lam__1___closed__0;
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_75);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_108 = !lean_is_exclusive(x_10);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_10, 0);
lean_dec(x_109);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_1);
lean_ctor_set(x_10, 0, x_110);
return x_10;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_10, 1);
lean_inc(x_111);
lean_dec(x_10);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_1);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_Grind_isUnfoldReducibleTarget___redArg(x_1, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec_ref(x_10);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_unfoldReducible_x27___lam__0___boxed), 9, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_unfoldReducible_x27___lam__1___boxed), 9, 0);
x_20 = l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2(x_1, x_19, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getReducibilityStatus___at___Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_getReducibilityStatus___at___Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isReducible___at___Lean_Meta_Grind_unfoldReducible_x27_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = l_Array_mapMUnsafe_map___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__2(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Expr_withAppAux___at___Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__2(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible_x27___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_unfoldReducible_x27___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_unfoldReducible_x27___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_unfoldReducible_x27___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_6 = lean_st_ref_get(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = l_Lean_instantiateMVarsCore(x_9, x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_st_ref_take(x_2, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_12);
x_18 = lean_st_ref_set(x_2, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_14, 1);
x_24 = lean_ctor_get(x_14, 2);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_st_ref_set(x_2, x_27, x_15);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg(x_1, x_7, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_preprocess___closed__1;
x_2 = l_Lean_Meta_Grind_preprocess___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_preprocess___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n===>\n", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_preprocess___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg(x_1, x_7, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_12);
x_14 = l_Lean_Meta_Grind_simpCore(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_17);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_18 = l_Lean_Meta_Grind_unfoldReducible_x27(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_21 = l_Lean_Meta_Grind_abstractNestedProofs___redArg(x_19, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_24 = l_Lean_Meta_Grind_markNestedSubsingletons(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
lean_inc(x_9);
lean_inc_ref(x_8);
x_27 = l_Lean_Meta_Grind_eraseIrrelevantMData(x_25, x_8, x_9, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_30 = l_Lean_Meta_Grind_foldProjs(x_28, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
lean_inc(x_9);
lean_inc_ref(x_8);
x_33 = l_Lean_Meta_Grind_normalizeLevels(x_31, x_8, x_9, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_36 = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(x_34, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_37);
x_39 = l_Lean_Meta_Simp_Result_mkEqTrans(x_15, x_37, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_43);
lean_dec(x_37);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_44 = l_Lean_Meta_Grind_replacePreMatchCond(x_43, x_6, x_7, x_8, x_9, x_42);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_46);
x_48 = l_Lean_Meta_Simp_Result_mkEqTrans(x_41, x_46, x_6, x_7, x_8, x_9, x_47);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
x_52 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_52);
lean_dec(x_46);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_53 = l_Lean_Meta_Grind_Canon_canon(x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_51);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l_Lean_Meta_Grind_shareCommon___redArg(x_54, x_5, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
x_69 = l_Lean_Meta_Grind_preprocess___closed__2;
x_70 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_69, x_8, x_58);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
lean_free_object(x_48);
lean_free_object(x_44);
lean_free_object(x_39);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec_ref(x_70);
x_60 = x_73;
goto block_68;
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_70);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_70, 1);
x_76 = lean_ctor_get(x_70, 0);
lean_dec(x_76);
x_77 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = l_Lean_Meta_Grind_preprocess___closed__4;
x_80 = l_Lean_MessageData_ofExpr(x_12);
lean_ctor_set_tag(x_70, 7);
lean_ctor_set(x_70, 1, x_80);
lean_ctor_set(x_70, 0, x_79);
x_81 = l_Lean_Meta_Grind_preprocess___closed__6;
lean_ctor_set_tag(x_48, 7);
lean_ctor_set(x_48, 1, x_81);
lean_ctor_set(x_48, 0, x_70);
lean_inc(x_57);
x_82 = l_Lean_MessageData_ofExpr(x_57);
lean_ctor_set_tag(x_44, 7);
lean_ctor_set(x_44, 1, x_82);
lean_ctor_set(x_44, 0, x_48);
lean_ctor_set_tag(x_39, 7);
lean_ctor_set(x_39, 1, x_79);
lean_ctor_set(x_39, 0, x_44);
x_83 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_69, x_39, x_6, x_7, x_8, x_9, x_78);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec_ref(x_83);
x_60 = x_84;
goto block_68;
}
else
{
uint8_t x_85; 
lean_free_object(x_70);
lean_dec(x_59);
lean_dec(x_57);
lean_free_object(x_48);
lean_dec(x_50);
lean_free_object(x_44);
lean_free_object(x_39);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_85 = !lean_is_exclusive(x_77);
if (x_85 == 0)
{
return x_77;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_77, 0);
x_87 = lean_ctor_get(x_77, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_77);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_70, 1);
lean_inc(x_89);
lean_dec(x_70);
x_90 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_89);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec_ref(x_90);
x_92 = l_Lean_Meta_Grind_preprocess___closed__4;
x_93 = l_Lean_MessageData_ofExpr(x_12);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_Meta_Grind_preprocess___closed__6;
lean_ctor_set_tag(x_48, 7);
lean_ctor_set(x_48, 1, x_95);
lean_ctor_set(x_48, 0, x_94);
lean_inc(x_57);
x_96 = l_Lean_MessageData_ofExpr(x_57);
lean_ctor_set_tag(x_44, 7);
lean_ctor_set(x_44, 1, x_96);
lean_ctor_set(x_44, 0, x_48);
lean_ctor_set_tag(x_39, 7);
lean_ctor_set(x_39, 1, x_92);
lean_ctor_set(x_39, 0, x_44);
x_97 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_69, x_39, x_6, x_7, x_8, x_9, x_91);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec_ref(x_97);
x_60 = x_98;
goto block_68;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_59);
lean_dec(x_57);
lean_free_object(x_48);
lean_dec(x_50);
lean_free_object(x_44);
lean_free_object(x_39);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_99 = lean_ctor_get(x_90, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_90, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_101 = x_90;
} else {
 lean_dec_ref(x_90);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
block_68:
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_50);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_50, 0);
lean_dec(x_62);
lean_ctor_set(x_50, 0, x_57);
if (lean_is_scalar(x_59)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_59;
}
lean_ctor_set(x_63, 0, x_50);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
else
{
lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_50, 1);
x_65 = lean_ctor_get_uint8(x_50, sizeof(void*)*2);
lean_inc(x_64);
lean_dec(x_50);
x_66 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_66, 0, x_57);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*2, x_65);
if (lean_is_scalar(x_59)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_59;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_60);
return x_67;
}
}
}
else
{
uint8_t x_103; 
lean_free_object(x_48);
lean_dec(x_50);
lean_free_object(x_44);
lean_free_object(x_39);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_53);
if (x_103 == 0)
{
return x_53;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_53, 0);
x_105 = lean_ctor_get(x_53, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_53);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_48, 0);
x_108 = lean_ctor_get(x_48, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_48);
x_109 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_109);
lean_dec(x_46);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_110 = l_Lean_Meta_Grind_Canon_canon(x_109, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_108);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec_ref(x_110);
x_113 = l_Lean_Meta_Grind_shareCommon___redArg(x_111, x_5, x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
x_124 = l_Lean_Meta_Grind_preprocess___closed__2;
x_125 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_124, x_8, x_115);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; 
lean_free_object(x_44);
lean_free_object(x_39);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec_ref(x_125);
x_117 = x_128;
goto block_123;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_130 = x_125;
} else {
 lean_dec_ref(x_125);
 x_130 = lean_box(0);
}
x_131 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_129);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = l_Lean_Meta_Grind_preprocess___closed__4;
x_134 = l_Lean_MessageData_ofExpr(x_12);
if (lean_is_scalar(x_130)) {
 x_135 = lean_alloc_ctor(7, 2, 0);
} else {
 x_135 = x_130;
 lean_ctor_set_tag(x_135, 7);
}
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_Meta_Grind_preprocess___closed__6;
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
lean_inc(x_114);
x_138 = l_Lean_MessageData_ofExpr(x_114);
lean_ctor_set_tag(x_44, 7);
lean_ctor_set(x_44, 1, x_138);
lean_ctor_set(x_44, 0, x_137);
lean_ctor_set_tag(x_39, 7);
lean_ctor_set(x_39, 1, x_133);
lean_ctor_set(x_39, 0, x_44);
x_139 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_124, x_39, x_6, x_7, x_8, x_9, x_132);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec_ref(x_139);
x_117 = x_140;
goto block_123;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_130);
lean_dec(x_116);
lean_dec(x_114);
lean_dec(x_107);
lean_free_object(x_44);
lean_free_object(x_39);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_141 = lean_ctor_get(x_131, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_131, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_143 = x_131;
} else {
 lean_dec_ref(x_131);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
block_123:
{
lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_ctor_get(x_107, 1);
lean_inc(x_118);
x_119 = lean_ctor_get_uint8(x_107, sizeof(void*)*2);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_120 = x_107;
} else {
 lean_dec_ref(x_107);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 2, 1);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_114);
lean_ctor_set(x_121, 1, x_118);
lean_ctor_set_uint8(x_121, sizeof(void*)*2, x_119);
if (lean_is_scalar(x_116)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_116;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_117);
return x_122;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_107);
lean_free_object(x_44);
lean_free_object(x_39);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_145 = lean_ctor_get(x_110, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_110, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_147 = x_110;
} else {
 lean_dec_ref(x_110);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
}
else
{
lean_free_object(x_44);
lean_dec(x_46);
lean_free_object(x_39);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_48;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_44, 0);
x_150 = lean_ctor_get(x_44, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_44);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_149);
x_151 = l_Lean_Meta_Simp_Result_mkEqTrans(x_41, x_149, x_6, x_7, x_8, x_9, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_154 = x_151;
} else {
 lean_dec_ref(x_151);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_149, 0);
lean_inc_ref(x_155);
lean_dec(x_149);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_156 = l_Lean_Meta_Grind_Canon_canon(x_155, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_153);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec_ref(x_156);
x_159 = l_Lean_Meta_Grind_shareCommon___redArg(x_157, x_5, x_158);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_162 = x_159;
} else {
 lean_dec_ref(x_159);
 x_162 = lean_box(0);
}
x_170 = l_Lean_Meta_Grind_preprocess___closed__2;
x_171 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_170, x_8, x_161);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_unbox(x_172);
lean_dec(x_172);
if (x_173 == 0)
{
lean_object* x_174; 
lean_dec(x_154);
lean_free_object(x_39);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec_ref(x_171);
x_163 = x_174;
goto block_169;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_171, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_176 = x_171;
} else {
 lean_dec_ref(x_171);
 x_176 = lean_box(0);
}
x_177 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_175);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec_ref(x_177);
x_179 = l_Lean_Meta_Grind_preprocess___closed__4;
x_180 = l_Lean_MessageData_ofExpr(x_12);
if (lean_is_scalar(x_176)) {
 x_181 = lean_alloc_ctor(7, 2, 0);
} else {
 x_181 = x_176;
 lean_ctor_set_tag(x_181, 7);
}
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = l_Lean_Meta_Grind_preprocess___closed__6;
if (lean_is_scalar(x_154)) {
 x_183 = lean_alloc_ctor(7, 2, 0);
} else {
 x_183 = x_154;
 lean_ctor_set_tag(x_183, 7);
}
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
lean_inc(x_160);
x_184 = l_Lean_MessageData_ofExpr(x_160);
x_185 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
lean_ctor_set_tag(x_39, 7);
lean_ctor_set(x_39, 1, x_179);
lean_ctor_set(x_39, 0, x_185);
x_186 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_170, x_39, x_6, x_7, x_8, x_9, x_178);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec_ref(x_186);
x_163 = x_187;
goto block_169;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_176);
lean_dec(x_162);
lean_dec(x_160);
lean_dec(x_154);
lean_dec(x_152);
lean_free_object(x_39);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_188 = lean_ctor_get(x_177, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_177, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_190 = x_177;
} else {
 lean_dec_ref(x_177);
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
block_169:
{
lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_164 = lean_ctor_get(x_152, 1);
lean_inc(x_164);
x_165 = lean_ctor_get_uint8(x_152, sizeof(void*)*2);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_166 = x_152;
} else {
 lean_dec_ref(x_152);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 2, 1);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_160);
lean_ctor_set(x_167, 1, x_164);
lean_ctor_set_uint8(x_167, sizeof(void*)*2, x_165);
if (lean_is_scalar(x_162)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_162;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_163);
return x_168;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_154);
lean_dec(x_152);
lean_free_object(x_39);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_192 = lean_ctor_get(x_156, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_156, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_194 = x_156;
} else {
 lean_dec_ref(x_156);
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
else
{
lean_dec(x_149);
lean_free_object(x_39);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_151;
}
}
}
else
{
lean_free_object(x_39);
lean_dec(x_41);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_44;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_196 = lean_ctor_get(x_39, 0);
x_197 = lean_ctor_get(x_39, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_39);
x_198 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_198);
lean_dec(x_37);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_199 = l_Lean_Meta_Grind_replacePreMatchCond(x_198, x_6, x_7, x_8, x_9, x_197);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_202 = x_199;
} else {
 lean_dec_ref(x_199);
 x_202 = lean_box(0);
}
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_200);
x_203 = l_Lean_Meta_Simp_Result_mkEqTrans(x_196, x_200, x_6, x_7, x_8, x_9, x_201);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_206 = x_203;
} else {
 lean_dec_ref(x_203);
 x_206 = lean_box(0);
}
x_207 = lean_ctor_get(x_200, 0);
lean_inc_ref(x_207);
lean_dec(x_200);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_208 = l_Lean_Meta_Grind_Canon_canon(x_207, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_205);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec_ref(x_208);
x_211 = l_Lean_Meta_Grind_shareCommon___redArg(x_209, x_5, x_210);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_214 = x_211;
} else {
 lean_dec_ref(x_211);
 x_214 = lean_box(0);
}
x_222 = l_Lean_Meta_Grind_preprocess___closed__2;
x_223 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_222, x_8, x_213);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_unbox(x_224);
lean_dec(x_224);
if (x_225 == 0)
{
lean_object* x_226; 
lean_dec(x_206);
lean_dec(x_202);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_226 = lean_ctor_get(x_223, 1);
lean_inc(x_226);
lean_dec_ref(x_223);
x_215 = x_226;
goto block_221;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_223, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_228 = x_223;
} else {
 lean_dec_ref(x_223);
 x_228 = lean_box(0);
}
x_229 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_227);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec_ref(x_229);
x_231 = l_Lean_Meta_Grind_preprocess___closed__4;
x_232 = l_Lean_MessageData_ofExpr(x_12);
if (lean_is_scalar(x_228)) {
 x_233 = lean_alloc_ctor(7, 2, 0);
} else {
 x_233 = x_228;
 lean_ctor_set_tag(x_233, 7);
}
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
x_234 = l_Lean_Meta_Grind_preprocess___closed__6;
if (lean_is_scalar(x_206)) {
 x_235 = lean_alloc_ctor(7, 2, 0);
} else {
 x_235 = x_206;
 lean_ctor_set_tag(x_235, 7);
}
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
lean_inc(x_212);
x_236 = l_Lean_MessageData_ofExpr(x_212);
if (lean_is_scalar(x_202)) {
 x_237 = lean_alloc_ctor(7, 2, 0);
} else {
 x_237 = x_202;
 lean_ctor_set_tag(x_237, 7);
}
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_231);
x_239 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_222, x_238, x_6, x_7, x_8, x_9, x_230);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec_ref(x_239);
x_215 = x_240;
goto block_221;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_228);
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_202);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_241 = lean_ctor_get(x_229, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_229, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_243 = x_229;
} else {
 lean_dec_ref(x_229);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
block_221:
{
lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_216 = lean_ctor_get(x_204, 1);
lean_inc(x_216);
x_217 = lean_ctor_get_uint8(x_204, sizeof(void*)*2);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_218 = x_204;
} else {
 lean_dec_ref(x_204);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(0, 2, 1);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_212);
lean_ctor_set(x_219, 1, x_216);
lean_ctor_set_uint8(x_219, sizeof(void*)*2, x_217);
if (lean_is_scalar(x_214)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_214;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_215);
return x_220;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_206);
lean_dec(x_204);
lean_dec(x_202);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_245 = lean_ctor_get(x_208, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_208, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_247 = x_208;
} else {
 lean_dec_ref(x_208);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
else
{
lean_dec(x_202);
lean_dec(x_200);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_203;
}
}
else
{
lean_dec(x_196);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_199;
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_39;
}
}
else
{
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_36;
}
}
else
{
uint8_t x_249; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_249 = !lean_is_exclusive(x_33);
if (x_249 == 0)
{
return x_33;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_33, 0);
x_251 = lean_ctor_get(x_33, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_33);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
else
{
uint8_t x_253; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_253 = !lean_is_exclusive(x_30);
if (x_253 == 0)
{
return x_30;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_30, 0);
x_255 = lean_ctor_get(x_30, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_30);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
else
{
uint8_t x_257; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_257 = !lean_is_exclusive(x_27);
if (x_257 == 0)
{
return x_27;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_27, 0);
x_259 = lean_ctor_get(x_27, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_27);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
else
{
uint8_t x_261; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_261 = !lean_is_exclusive(x_24);
if (x_261 == 0)
{
return x_24;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_24, 0);
x_263 = lean_ctor_get(x_24, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_24);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
else
{
uint8_t x_265; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_265 = !lean_is_exclusive(x_21);
if (x_265 == 0)
{
return x_21;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_21, 0);
x_267 = lean_ctor_get(x_21, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_21);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
}
else
{
uint8_t x_269; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_269 = !lean_is_exclusive(x_18);
if (x_269 == 0)
{
return x_18;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_18, 0);
x_271 = lean_ctor_get(x_18, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_18);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pushNewFact", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_pushNewFact_x27___closed__1;
x_2 = l_Lean_Meta_Grind_pushNewFact_x27___closed__0;
x_3 = l_Lean_Meta_Grind_preprocess___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ==> ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_pushNewFact_x27___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mp", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_pushNewFact_x27___closed__6;
x_2 = l_Lean_Meta_Grind_pushNewFact_x27___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_pushNewFact_x27___closed__8;
x_2 = l_Lean_Meta_Grind_pushNewFact_x27___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_4);
lean_inc_ref(x_1);
x_13 = l_Lean_Meta_Grind_preprocess(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_61; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
x_61 = x_2;
goto block_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_17, 0);
lean_inc(x_91);
lean_dec(x_17);
x_92 = l_Lean_Meta_Grind_pushNewFact_x27___closed__9;
lean_inc_ref(x_16);
lean_inc_ref(x_1);
x_93 = l_Lean_mkApp4(x_92, x_1, x_16, x_91, x_2);
x_61 = x_93;
goto block_90;
}
block_60:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_st_ref_take(x_19, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_22, 7);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_3);
x_27 = lean_array_push(x_25, x_26);
lean_ctor_set(x_22, 7, x_27);
x_28 = lean_st_ref_set(x_19, x_22, x_23);
lean_dec(x_19);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
x_37 = lean_ctor_get(x_22, 2);
x_38 = lean_ctor_get(x_22, 3);
x_39 = lean_ctor_get(x_22, 4);
x_40 = lean_ctor_get(x_22, 5);
x_41 = lean_ctor_get(x_22, 6);
x_42 = lean_ctor_get(x_22, 7);
x_43 = lean_ctor_get_uint8(x_22, sizeof(void*)*16);
x_44 = lean_ctor_get(x_22, 8);
x_45 = lean_ctor_get(x_22, 9);
x_46 = lean_ctor_get(x_22, 10);
x_47 = lean_ctor_get(x_22, 11);
x_48 = lean_ctor_get(x_22, 12);
x_49 = lean_ctor_get(x_22, 13);
x_50 = lean_ctor_get(x_22, 14);
x_51 = lean_ctor_get(x_22, 15);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_16);
lean_ctor_set(x_52, 1, x_18);
lean_ctor_set(x_52, 2, x_3);
x_53 = lean_array_push(x_42, x_52);
x_54 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_54, 0, x_35);
lean_ctor_set(x_54, 1, x_36);
lean_ctor_set(x_54, 2, x_37);
lean_ctor_set(x_54, 3, x_38);
lean_ctor_set(x_54, 4, x_39);
lean_ctor_set(x_54, 5, x_40);
lean_ctor_set(x_54, 6, x_41);
lean_ctor_set(x_54, 7, x_53);
lean_ctor_set(x_54, 8, x_44);
lean_ctor_set(x_54, 9, x_45);
lean_ctor_set(x_54, 10, x_46);
lean_ctor_set(x_54, 11, x_47);
lean_ctor_set(x_54, 12, x_48);
lean_ctor_set(x_54, 13, x_49);
lean_ctor_set(x_54, 14, x_50);
lean_ctor_set(x_54, 15, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*16, x_43);
x_55 = lean_st_ref_set(x_19, x_54, x_23);
lean_dec(x_19);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = lean_box(0);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
block_90:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = l_Lean_Meta_Grind_pushNewFact_x27___closed__2;
x_63 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_62, x_10, x_15);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec_ref(x_63);
x_18 = x_61;
x_19 = x_4;
x_20 = x_66;
goto block_60;
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_68 = lean_ctor_get(x_63, 1);
x_69 = lean_ctor_get(x_63, 0);
lean_dec(x_69);
x_70 = l_Lean_Meta_Grind_preprocess___closed__4;
x_71 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_63, 7);
lean_ctor_set(x_63, 1, x_71);
lean_ctor_set(x_63, 0, x_70);
x_72 = l_Lean_Meta_Grind_pushNewFact_x27___closed__4;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_63);
lean_ctor_set(x_73, 1, x_72);
lean_inc_ref(x_16);
x_74 = l_Lean_MessageData_ofExpr(x_16);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_70);
x_77 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_62, x_76, x_8, x_9, x_10, x_11, x_68);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec_ref(x_77);
x_18 = x_61;
x_19 = x_4;
x_20 = x_78;
goto block_60;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_79 = lean_ctor_get(x_63, 1);
lean_inc(x_79);
lean_dec(x_63);
x_80 = l_Lean_Meta_Grind_preprocess___closed__4;
x_81 = l_Lean_MessageData_ofExpr(x_1);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_Meta_Grind_pushNewFact_x27___closed__4;
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
lean_inc_ref(x_16);
x_85 = l_Lean_MessageData_ofExpr(x_16);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_80);
x_88 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_62, x_87, x_8, x_9, x_10, x_11, x_79);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec_ref(x_88);
x_18 = x_61;
x_19 = x_4;
x_20 = x_89;
goto block_60;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_94 = !lean_is_exclusive(x_13);
if (x_94 == 0)
{
return x_13;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_13, 0);
x_96 = lean_ctor_get(x_13, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_13);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_1);
x_12 = lean_infer_type(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Lean_Meta_Grind_pushNewFact_x27___closed__2;
x_16 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_15, x_9, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = l_Lean_Meta_Grind_pushNewFact_x27(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_16, 1);
x_23 = lean_ctor_get(x_16, 0);
lean_dec(x_23);
x_24 = l_Lean_Meta_Grind_preprocess___closed__4;
lean_inc(x_13);
x_25 = l_Lean_MessageData_ofExpr(x_13);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_25);
lean_ctor_set(x_16, 0, x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_15, x_26, x_7, x_8, x_9, x_10, x_22);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l_Lean_Meta_Grind_pushNewFact_x27(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_dec(x_16);
x_31 = l_Lean_Meta_Grind_preprocess___closed__4;
lean_inc(x_13);
x_32 = l_Lean_MessageData_ofExpr(x_13);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_15, x_34, x_7, x_8, x_9, x_10, x_30);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l_Lean_Meta_Grind_pushNewFact_x27(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
return x_12;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_12, 0);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_12);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Canon(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Canon(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_simpCore___lam__1___closed__0 = _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__1___closed__0);
l_Lean_Meta_Grind_simpCore___lam__1___closed__1 = _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__1___closed__1);
l_Lean_Meta_Grind_simpCore___lam__1___closed__2 = _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__1___closed__2);
l_Lean_Meta_Grind_simpCore___lam__1___closed__3 = _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__1___closed__3);
l_Lean_Meta_Grind_simpCore___lam__1___closed__4 = _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__1___closed__4);
l_Lean_Meta_Grind_simpCore___lam__1___closed__5 = _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__1___closed__5);
l_Lean_Meta_Grind_simpCore___lam__1___closed__6 = _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__1___closed__6);
l_Lean_Meta_Grind_simpCore___lam__1___closed__7 = _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__1___closed__7);
l_Lean_Meta_Grind_simpCore___lam__1___closed__8 = _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__1___closed__8);
l_Lean_Meta_Grind_simpCore___lam__1___closed__9 = _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__1___closed__9);
l_Lean_Meta_Grind_simpCore___lam__1___closed__10 = _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__1___closed__10);
l_Lean_Meta_Grind_simpCore___lam__1___closed__11 = _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__1___closed__11);
l_Lean_Meta_Grind_simpCore___lam__1___closed__12 = _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__1___closed__12);
l_Lean_Meta_Grind_simpCore___lam__1___closed__13 = _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__1___closed__13);
l_Lean_Meta_Grind_simpCore___lam__1___closed__14 = _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__14();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__1___closed__14);
l_Lean_Meta_Grind_simpCore___lam__1___closed__15 = _init_l_Lean_Meta_Grind_simpCore___lam__1___closed__15();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___lam__1___closed__15);
l_Lean_Meta_Grind_simpCore___closed__0 = _init_l_Lean_Meta_Grind_simpCore___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_simpCore___closed__0);
l_Lean_Meta_Grind_dsimpCore___closed__0 = _init_l_Lean_Meta_Grind_dsimpCore___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_dsimpCore___closed__0);
l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__1___closed__0 = _init_l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__1___closed__0();
lean_mark_persistent(l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___lam__1___closed__0);
l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___boxed__const__1 = _init_l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___boxed__const__1();
lean_mark_persistent(l_Lean_Core_transform_visit___at___Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2_spec__2___boxed__const__1);
l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2___closed__0 = _init_l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2___closed__0();
lean_mark_persistent(l_Lean_Core_transform___at___Lean_Meta_Grind_unfoldReducible_x27_spec__2___closed__0);
l_Lean_Meta_Grind_unfoldReducible_x27___lam__1___closed__0 = _init_l_Lean_Meta_Grind_unfoldReducible_x27___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_unfoldReducible_x27___lam__1___closed__0);
l_Lean_Meta_Grind_preprocess___closed__0 = _init_l_Lean_Meta_Grind_preprocess___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__0);
l_Lean_Meta_Grind_preprocess___closed__1 = _init_l_Lean_Meta_Grind_preprocess___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__1);
l_Lean_Meta_Grind_preprocess___closed__2 = _init_l_Lean_Meta_Grind_preprocess___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__2);
l_Lean_Meta_Grind_preprocess___closed__3 = _init_l_Lean_Meta_Grind_preprocess___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__3);
l_Lean_Meta_Grind_preprocess___closed__4 = _init_l_Lean_Meta_Grind_preprocess___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__4);
l_Lean_Meta_Grind_preprocess___closed__5 = _init_l_Lean_Meta_Grind_preprocess___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__5);
l_Lean_Meta_Grind_preprocess___closed__6 = _init_l_Lean_Meta_Grind_preprocess___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__6);
l_Lean_Meta_Grind_pushNewFact_x27___closed__0 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__0);
l_Lean_Meta_Grind_pushNewFact_x27___closed__1 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__1);
l_Lean_Meta_Grind_pushNewFact_x27___closed__2 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__2);
l_Lean_Meta_Grind_pushNewFact_x27___closed__3 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__3);
l_Lean_Meta_Grind_pushNewFact_x27___closed__4 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__4);
l_Lean_Meta_Grind_pushNewFact_x27___closed__5 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__5);
l_Lean_Meta_Grind_pushNewFact_x27___closed__6 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__6);
l_Lean_Meta_Grind_pushNewFact_x27___closed__7 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__7);
l_Lean_Meta_Grind_pushNewFact_x27___closed__8 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__8);
l_Lean_Meta_Grind_pushNewFact_x27___closed__9 = _init_l_Lean_Meta_Grind_pushNewFact_x27___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_pushNewFact_x27___closed__9);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
