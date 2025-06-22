// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.EqResolution
// Imports: Lean.Meta.AppBuilder Lean.Meta.MatchUtil Lean.Util.ForEachExpr
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eqResolution___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__2;
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_eqResolution___closed__0;
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__2;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Lean_Meta_Grind_eqResolution___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_checked_assign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__0;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__1;
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eqResolution(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__1;
lean_object* l_Lean_MVarId_isDelayedAssigned___at___Lean_Meta_getMVarsNoDelayed_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t l_Array_contains___at___Lean_Meta_arrowDomainsN_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__0;
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__1;
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchNot_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_eqResolution___lam__0___closed__0;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__0;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__3;
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Meta_forallMetaTelescopeReducing(x_1, x_7, x_9, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_16);
x_18 = l_Lean_Meta_matchNot_x3f(x_16, x_2, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_12, 0, x_14);
lean_ctor_set(x_18, 0, x_12);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
lean_ctor_set(x_12, 0, x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_box(0);
x_26 = lean_unbox(x_8);
x_27 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_19, x_26, x_25, x_2, x_3, x_4, x_5, x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_array_push(x_14, x_29);
x_31 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2;
lean_ctor_set(x_12, 1, x_31);
lean_ctor_set(x_12, 0, x_30);
lean_ctor_set(x_27, 0, x_12);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = lean_array_push(x_14, x_32);
x_35 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2;
lean_ctor_set(x_12, 1, x_35);
lean_ctor_set(x_12, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_12);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_12);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_12, 1);
lean_inc(x_41);
lean_dec(x_12);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_41);
x_42 = l_Lean_Meta_matchNot_x3f(x_41, x_2, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_14);
lean_ctor_set(x_46, 1, x_41);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_41);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_dec(x_42);
x_49 = lean_box(0);
x_50 = lean_unbox(x_8);
x_51 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_43, x_50, x_49, x_2, x_3, x_4, x_5, x_48);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = lean_array_push(x_14, x_52);
x_56 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2;
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_ctor_get(x_42, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_42, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_61 = x_42;
} else {
 lean_dec_ref(x_42);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_10);
if (x_63 == 0)
{
return x_10;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_10, 0);
x_65 = lean_ctor_get(x_10, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_10);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_113; lean_object* x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; uint64_t x_118; uint64_t x_119; uint64_t x_120; uint64_t x_121; size_t x_122; size_t x_123; size_t x_124; size_t x_125; size_t x_126; lean_object* x_127; uint8_t x_128; 
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 2);
lean_inc(x_22);
x_113 = lean_ctor_get(x_21, 1);
lean_inc(x_113);
x_114 = lean_array_get_size(x_113);
x_115 = l_Lean_Expr_hash(x_2);
x_116 = 32;
x_117 = lean_uint64_shift_right(x_115, x_116);
x_118 = lean_uint64_xor(x_115, x_117);
x_119 = 16;
x_120 = lean_uint64_shift_right(x_118, x_119);
x_121 = lean_uint64_xor(x_118, x_120);
x_122 = lean_uint64_to_usize(x_121);
x_123 = lean_usize_of_nat(x_114);
lean_dec(x_114);
x_124 = 1;
x_125 = lean_usize_sub(x_123, x_124);
x_126 = lean_usize_land(x_122, x_125);
x_127 = lean_array_uget(x_113, x_126);
lean_dec(x_113);
x_128 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_2, x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; size_t x_132; size_t x_133; size_t x_134; lean_object* x_135; uint8_t x_136; 
x_129 = lean_ctor_get(x_20, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_20, 1);
lean_inc(x_130);
x_131 = lean_array_get_size(x_130);
x_132 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_133 = lean_usize_sub(x_132, x_124);
x_134 = lean_usize_land(x_122, x_133);
x_135 = lean_array_uget(x_130, x_134);
x_136 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_2, x_135);
if (x_136 == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_3);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_3, 2);
lean_dec(x_138);
x_139 = lean_ctor_get(x_3, 1);
lean_dec(x_139);
x_140 = lean_ctor_get(x_3, 0);
lean_dec(x_140);
if (x_136 == 0)
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_20);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_142 = lean_ctor_get(x_20, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_20, 0);
lean_dec(x_143);
x_144 = lean_box(0);
x_145 = lean_unsigned_to_nat(1u);
x_146 = lean_nat_add(x_129, x_145);
lean_dec(x_129);
lean_inc(x_2);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 2, x_135);
lean_ctor_set(x_3, 1, x_144);
lean_ctor_set(x_3, 0, x_2);
x_147 = lean_array_uset(x_130, x_134, x_3);
x_148 = lean_unsigned_to_nat(4u);
x_149 = lean_nat_mul(x_146, x_148);
x_150 = lean_unsigned_to_nat(3u);
x_151 = lean_nat_div(x_149, x_150);
lean_dec(x_149);
x_152 = lean_array_get_size(x_147);
x_153 = lean_nat_dec_le(x_151, x_152);
lean_dec(x_152);
lean_dec(x_151);
if (x_153 == 0)
{
lean_object* x_154; 
x_154 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_147);
lean_ctor_set(x_20, 1, x_154);
lean_ctor_set(x_20, 0, x_146);
x_23 = x_20;
goto block_112;
}
else
{
lean_ctor_set(x_20, 1, x_147);
lean_ctor_set(x_20, 0, x_146);
x_23 = x_20;
goto block_112;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
lean_dec(x_20);
x_155 = lean_box(0);
x_156 = lean_unsigned_to_nat(1u);
x_157 = lean_nat_add(x_129, x_156);
lean_dec(x_129);
lean_inc(x_2);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 2, x_135);
lean_ctor_set(x_3, 1, x_155);
lean_ctor_set(x_3, 0, x_2);
x_158 = lean_array_uset(x_130, x_134, x_3);
x_159 = lean_unsigned_to_nat(4u);
x_160 = lean_nat_mul(x_157, x_159);
x_161 = lean_unsigned_to_nat(3u);
x_162 = lean_nat_div(x_160, x_161);
lean_dec(x_160);
x_163 = lean_array_get_size(x_158);
x_164 = lean_nat_dec_le(x_162, x_163);
lean_dec(x_163);
lean_dec(x_162);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_158);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_157);
lean_ctor_set(x_166, 1, x_165);
x_23 = x_166;
goto block_112;
}
else
{
lean_object* x_167; 
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_157);
lean_ctor_set(x_167, 1, x_158);
x_23 = x_167;
goto block_112;
}
}
}
else
{
lean_free_object(x_3);
lean_dec(x_135);
lean_dec(x_130);
lean_dec(x_129);
x_23 = x_20;
goto block_112;
}
}
else
{
lean_dec(x_3);
if (x_136 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_168 = x_20;
} else {
 lean_dec_ref(x_20);
 x_168 = lean_box(0);
}
x_169 = lean_box(0);
x_170 = lean_unsigned_to_nat(1u);
x_171 = lean_nat_add(x_129, x_170);
lean_dec(x_129);
lean_inc(x_2);
x_172 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_172, 0, x_2);
lean_ctor_set(x_172, 1, x_169);
lean_ctor_set(x_172, 2, x_135);
x_173 = lean_array_uset(x_130, x_134, x_172);
x_174 = lean_unsigned_to_nat(4u);
x_175 = lean_nat_mul(x_171, x_174);
x_176 = lean_unsigned_to_nat(3u);
x_177 = lean_nat_div(x_175, x_176);
lean_dec(x_175);
x_178 = lean_array_get_size(x_173);
x_179 = lean_nat_dec_le(x_177, x_178);
lean_dec(x_178);
lean_dec(x_177);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_173);
if (lean_is_scalar(x_168)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_168;
}
lean_ctor_set(x_181, 0, x_171);
lean_ctor_set(x_181, 1, x_180);
x_23 = x_181;
goto block_112;
}
else
{
lean_object* x_182; 
if (lean_is_scalar(x_168)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_168;
}
lean_ctor_set(x_182, 0, x_171);
lean_ctor_set(x_182, 1, x_173);
x_23 = x_182;
goto block_112;
}
}
else
{
lean_dec(x_135);
lean_dec(x_130);
lean_dec(x_129);
x_23 = x_20;
goto block_112;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_135);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_183 = !lean_is_exclusive(x_21);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_21, 1);
lean_dec(x_184);
x_185 = lean_ctor_get(x_21, 0);
lean_dec(x_185);
x_186 = lean_box(0);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_21, 0, x_186);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_21);
lean_ctor_set(x_187, 1, x_8);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_21);
x_188 = lean_box(0);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_3);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_8);
return x_190;
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_191 = !lean_is_exclusive(x_21);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_21, 1);
lean_dec(x_192);
x_193 = lean_ctor_get(x_21, 0);
lean_dec(x_193);
x_194 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0;
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_21, 0, x_194);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_21);
lean_ctor_set(x_195, 1, x_8);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_21);
x_196 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0;
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_3);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_8);
return x_198;
}
}
block_19:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_push(x_10, x_2);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
block_112:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_inc(x_2);
x_25 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf(x_1, x_2, x_24, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_26);
lean_dec(x_2);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; size_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; lean_object* x_51; uint8_t x_52; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 2);
x_34 = lean_ctor_get(x_28, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
x_37 = lean_box(0);
x_38 = lean_array_get_size(x_36);
x_39 = l_Lean_Expr_hash(x_2);
x_40 = 32;
x_41 = lean_uint64_shift_right(x_39, x_40);
x_42 = lean_uint64_xor(x_39, x_41);
x_43 = 16;
x_44 = lean_uint64_shift_right(x_42, x_43);
x_45 = lean_uint64_xor(x_42, x_44);
x_46 = lean_uint64_to_usize(x_45);
x_47 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_48 = 1;
x_49 = lean_usize_sub(x_47, x_48);
x_50 = lean_usize_land(x_46, x_49);
x_51 = lean_array_uget(x_36, x_50);
x_52 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_2, x_51);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_29);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_54 = lean_ctor_get(x_29, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_29, 0);
lean_dec(x_55);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_35, x_56);
lean_dec(x_35);
lean_inc(x_2);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 2, x_51);
lean_ctor_set(x_28, 1, x_37);
lean_ctor_set(x_28, 0, x_2);
x_58 = lean_array_uset(x_36, x_50, x_28);
x_59 = lean_unsigned_to_nat(4u);
x_60 = lean_nat_mul(x_57, x_59);
x_61 = lean_unsigned_to_nat(3u);
x_62 = lean_nat_div(x_60, x_61);
lean_dec(x_60);
x_63 = lean_array_get_size(x_58);
x_64 = lean_nat_dec_le(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_58);
lean_ctor_set(x_29, 1, x_65);
lean_ctor_set(x_29, 0, x_57);
x_9 = x_37;
x_10 = x_33;
x_11 = x_30;
x_12 = x_32;
x_13 = x_29;
goto block_19;
}
else
{
lean_ctor_set(x_29, 1, x_58);
lean_ctor_set(x_29, 0, x_57);
x_9 = x_37;
x_10 = x_33;
x_11 = x_30;
x_12 = x_32;
x_13 = x_29;
goto block_19;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_29);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_35, x_66);
lean_dec(x_35);
lean_inc(x_2);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 2, x_51);
lean_ctor_set(x_28, 1, x_37);
lean_ctor_set(x_28, 0, x_2);
x_68 = lean_array_uset(x_36, x_50, x_28);
x_69 = lean_unsigned_to_nat(4u);
x_70 = lean_nat_mul(x_67, x_69);
x_71 = lean_unsigned_to_nat(3u);
x_72 = lean_nat_div(x_70, x_71);
lean_dec(x_70);
x_73 = lean_array_get_size(x_68);
x_74 = lean_nat_dec_le(x_72, x_73);
lean_dec(x_73);
lean_dec(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_68);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
x_9 = x_37;
x_10 = x_33;
x_11 = x_30;
x_12 = x_32;
x_13 = x_76;
goto block_19;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_67);
lean_ctor_set(x_77, 1, x_68);
x_9 = x_37;
x_10 = x_33;
x_11 = x_30;
x_12 = x_32;
x_13 = x_77;
goto block_19;
}
}
}
else
{
lean_dec(x_51);
lean_dec(x_36);
lean_dec(x_35);
lean_free_object(x_28);
x_9 = x_37;
x_10 = x_33;
x_11 = x_30;
x_12 = x_32;
x_13 = x_29;
goto block_19;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; uint64_t x_88; uint64_t x_89; uint64_t x_90; size_t x_91; size_t x_92; size_t x_93; size_t x_94; size_t x_95; lean_object* x_96; uint8_t x_97; 
x_78 = lean_ctor_get(x_28, 0);
x_79 = lean_ctor_get(x_28, 2);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_28);
x_80 = lean_ctor_get(x_29, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_29, 1);
lean_inc(x_81);
x_82 = lean_box(0);
x_83 = lean_array_get_size(x_81);
x_84 = l_Lean_Expr_hash(x_2);
x_85 = 32;
x_86 = lean_uint64_shift_right(x_84, x_85);
x_87 = lean_uint64_xor(x_84, x_86);
x_88 = 16;
x_89 = lean_uint64_shift_right(x_87, x_88);
x_90 = lean_uint64_xor(x_87, x_89);
x_91 = lean_uint64_to_usize(x_90);
x_92 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_93 = 1;
x_94 = lean_usize_sub(x_92, x_93);
x_95 = lean_usize_land(x_91, x_94);
x_96 = lean_array_uget(x_81, x_95);
x_97 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_2, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_98 = x_29;
} else {
 lean_dec_ref(x_29);
 x_98 = lean_box(0);
}
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_nat_add(x_80, x_99);
lean_dec(x_80);
lean_inc(x_2);
x_101 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_101, 0, x_2);
lean_ctor_set(x_101, 1, x_82);
lean_ctor_set(x_101, 2, x_96);
x_102 = lean_array_uset(x_81, x_95, x_101);
x_103 = lean_unsigned_to_nat(4u);
x_104 = lean_nat_mul(x_100, x_103);
x_105 = lean_unsigned_to_nat(3u);
x_106 = lean_nat_div(x_104, x_105);
lean_dec(x_104);
x_107 = lean_array_get_size(x_102);
x_108 = lean_nat_dec_le(x_106, x_107);
lean_dec(x_107);
lean_dec(x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_102);
if (lean_is_scalar(x_98)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_98;
}
lean_ctor_set(x_110, 0, x_100);
lean_ctor_set(x_110, 1, x_109);
x_9 = x_82;
x_10 = x_79;
x_11 = x_30;
x_12 = x_78;
x_13 = x_110;
goto block_19;
}
else
{
lean_object* x_111; 
if (lean_is_scalar(x_98)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_98;
}
lean_ctor_set(x_111, 0, x_100);
lean_ctor_set(x_111, 1, x_102);
x_9 = x_82;
x_10 = x_79;
x_11 = x_30;
x_12 = x_78;
x_13 = x_111;
goto block_19;
}
}
else
{
lean_dec(x_96);
lean_dec(x_81);
lean_dec(x_80);
x_9 = x_82;
x_10 = x_79;
x_11 = x_30;
x_12 = x_78;
x_13 = x_29;
goto block_19;
}
}
}
}
else
{
lean_dec(x_2);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_hasMVar(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_st_ref_get(x_3, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_instantiateMVarsCore(x_12, x_1);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_st_ref_take(x_3, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_16);
x_22 = lean_st_ref_set(x_3, x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 0, x_25);
lean_ctor_set(x_22, 0, x_13);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
x_32 = lean_ctor_get(x_18, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_16);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_31);
lean_ctor_set(x_33, 4, x_32);
x_34 = lean_st_ref_set(x_3, x_33, x_19);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_15);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 0, x_37);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_13);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_39 = lean_ctor_get(x_13, 0);
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_13);
x_41 = lean_st_ref_take(x_3, x_11);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 4);
lean_inc(x_47);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 lean_ctor_release(x_42, 4);
 x_48 = x_42;
} else {
 lean_dec_ref(x_42);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 5, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_44);
lean_ctor_set(x_49, 2, x_45);
lean_ctor_set(x_49, 3, x_46);
lean_ctor_set(x_49, 4, x_47);
x_50 = lean_st_ref_set(x_3, x_49, x_43);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_39);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_2);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__0___redArg(x_1, x_2, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_19; uint8_t x_20; 
x_19 = lean_st_ref_get(x_3, x_9);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; size_t x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_94; size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; 
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_array_get_size(x_24);
x_27 = l_Lean_Expr_hash(x_2);
x_28 = 32;
x_29 = lean_uint64_shift_right(x_27, x_28);
x_30 = lean_uint64_xor(x_27, x_29);
x_31 = 16;
x_32 = lean_uint64_shift_right(x_30, x_31);
x_33 = lean_uint64_xor(x_30, x_32);
x_34 = lean_uint64_to_usize(x_33);
x_35 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_36 = 1;
x_100 = lean_usize_sub(x_35, x_36);
x_101 = lean_usize_land(x_34, x_100);
x_102 = lean_array_uget(x_24, x_101);
lean_dec(x_24);
x_103 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0___redArg(x_2, x_102);
lean_dec(x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
lean_free_object(x_21);
lean_free_object(x_19);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_104 = lean_apply_7(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_104) == 0)
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_104, 0);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_104, 1);
x_109 = lean_ctor_get(x_106, 0);
x_110 = lean_ctor_get(x_106, 1);
if (lean_obj_tag(x_109) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_106, 0, x_103);
return x_104;
}
else
{
lean_object* x_121; uint8_t x_122; 
lean_free_object(x_104);
x_121 = lean_ctor_get(x_109, 0);
lean_inc(x_121);
lean_dec(x_109);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_123 = lean_box(0);
x_124 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0;
lean_ctor_set(x_106, 0, x_124);
x_37 = x_106;
x_38 = x_123;
x_39 = x_108;
goto block_93;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_free_object(x_106);
x_125 = lean_ctor_get(x_2, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_2, 1);
lean_inc(x_126);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_127 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_125, x_3, x_110, x_5, x_6, x_7, x_8, x_108);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
if (lean_obj_tag(x_129) == 0)
{
lean_dec(x_128);
lean_dec(x_126);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_127;
goto block_99;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_126, x_3, x_131, x_5, x_6, x_7, x_8, x_130);
x_94 = x_132;
goto block_99;
}
}
else
{
lean_dec(x_126);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_127;
goto block_99;
}
}
case 6:
{
lean_object* x_133; lean_object* x_134; 
lean_free_object(x_106);
x_133 = lean_ctor_get(x_2, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_2, 2);
lean_inc(x_134);
x_111 = x_133;
x_112 = x_134;
x_113 = x_3;
goto block_120;
}
case 7:
{
lean_object* x_135; lean_object* x_136; 
lean_free_object(x_106);
x_135 = lean_ctor_get(x_2, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_2, 2);
lean_inc(x_136);
x_111 = x_135;
x_112 = x_136;
x_113 = x_3;
goto block_120;
}
case 8:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_free_object(x_106);
x_137 = lean_ctor_get(x_2, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_2, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_2, 3);
lean_inc(x_139);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_140 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_137, x_3, x_110, x_5, x_6, x_7, x_8, x_108);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_obj_tag(x_142) == 0)
{
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_140;
goto block_99;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_142);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec(x_141);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_145 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_138, x_3, x_144, x_5, x_6, x_7, x_8, x_143);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_dec(x_146);
lean_dec(x_139);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_145;
goto block_99;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_147);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec(x_146);
x_150 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_139, x_3, x_149, x_5, x_6, x_7, x_8, x_148);
x_94 = x_150;
goto block_99;
}
}
else
{
lean_dec(x_139);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_145;
goto block_99;
}
}
}
else
{
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_140;
goto block_99;
}
}
case 10:
{
lean_object* x_151; lean_object* x_152; 
lean_free_object(x_106);
x_151 = lean_ctor_get(x_2, 1);
lean_inc(x_151);
x_152 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_151, x_3, x_110, x_5, x_6, x_7, x_8, x_108);
x_94 = x_152;
goto block_99;
}
case 11:
{
lean_object* x_153; lean_object* x_154; 
lean_free_object(x_106);
x_153 = lean_ctor_get(x_2, 2);
lean_inc(x_153);
x_154 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_153, x_3, x_110, x_5, x_6, x_7, x_8, x_108);
x_94 = x_154;
goto block_99;
}
default: 
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_155 = lean_box(0);
x_156 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0;
lean_ctor_set(x_106, 0, x_156);
x_37 = x_106;
x_38 = x_155;
x_39 = x_108;
goto block_93;
}
}
}
}
block_120:
{
lean_object* x_114; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_114 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_111, x_113, x_110, x_5, x_6, x_7, x_8, x_108);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
if (lean_obj_tag(x_116) == 0)
{
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_114;
goto block_99;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_116);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_112, x_113, x_118, x_5, x_6, x_7, x_8, x_117);
x_94 = x_119;
goto block_99;
}
}
else
{
lean_dec(x_112);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_114;
goto block_99;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_157 = lean_ctor_get(x_104, 1);
x_158 = lean_ctor_get(x_106, 0);
x_159 = lean_ctor_get(x_106, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_106);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_170; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_103);
lean_ctor_set(x_170, 1, x_159);
lean_ctor_set(x_104, 0, x_170);
return x_104;
}
else
{
lean_object* x_171; uint8_t x_172; 
lean_free_object(x_104);
x_171 = lean_ctor_get(x_158, 0);
lean_inc(x_171);
lean_dec(x_158);
x_172 = lean_unbox(x_171);
lean_dec(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_173 = lean_box(0);
x_174 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0;
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_159);
x_37 = x_175;
x_38 = x_173;
x_39 = x_157;
goto block_93;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_2, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_2, 1);
lean_inc(x_177);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_178 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_176, x_3, x_159, x_5, x_6, x_7, x_8, x_157);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
if (lean_obj_tag(x_180) == 0)
{
lean_dec(x_179);
lean_dec(x_177);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_178;
goto block_99;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_180);
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
lean_dec(x_178);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
lean_dec(x_179);
x_183 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_177, x_3, x_182, x_5, x_6, x_7, x_8, x_181);
x_94 = x_183;
goto block_99;
}
}
else
{
lean_dec(x_177);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_178;
goto block_99;
}
}
case 6:
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_2, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_2, 2);
lean_inc(x_185);
x_160 = x_184;
x_161 = x_185;
x_162 = x_3;
goto block_169;
}
case 7:
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_2, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_2, 2);
lean_inc(x_187);
x_160 = x_186;
x_161 = x_187;
x_162 = x_3;
goto block_169;
}
case 8:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_188 = lean_ctor_get(x_2, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_2, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_2, 3);
lean_inc(x_190);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_191 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_188, x_3, x_159, x_5, x_6, x_7, x_8, x_157);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
lean_dec(x_192);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_191;
goto block_99;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_193);
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
lean_dec(x_191);
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
lean_dec(x_192);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_196 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_189, x_3, x_195, x_5, x_6, x_7, x_8, x_194);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
if (lean_obj_tag(x_198) == 0)
{
lean_dec(x_197);
lean_dec(x_190);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_196;
goto block_99;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_198);
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
lean_dec(x_196);
x_200 = lean_ctor_get(x_197, 1);
lean_inc(x_200);
lean_dec(x_197);
x_201 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_190, x_3, x_200, x_5, x_6, x_7, x_8, x_199);
x_94 = x_201;
goto block_99;
}
}
else
{
lean_dec(x_190);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_196;
goto block_99;
}
}
}
else
{
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_191;
goto block_99;
}
}
case 10:
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_2, 1);
lean_inc(x_202);
x_203 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_202, x_3, x_159, x_5, x_6, x_7, x_8, x_157);
x_94 = x_203;
goto block_99;
}
case 11:
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_2, 2);
lean_inc(x_204);
x_205 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_204, x_3, x_159, x_5, x_6, x_7, x_8, x_157);
x_94 = x_205;
goto block_99;
}
default: 
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_206 = lean_box(0);
x_207 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0;
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_159);
x_37 = x_208;
x_38 = x_206;
x_39 = x_157;
goto block_93;
}
}
}
}
block_169:
{
lean_object* x_163; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_163 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_160, x_162, x_159, x_5, x_6, x_7, x_8, x_157);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
if (lean_obj_tag(x_165) == 0)
{
lean_dec(x_164);
lean_dec(x_161);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_163;
goto block_99;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_165);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
lean_dec(x_164);
x_168 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_161, x_162, x_167, x_5, x_6, x_7, x_8, x_166);
x_94 = x_168;
goto block_99;
}
}
else
{
lean_dec(x_161);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_163;
goto block_99;
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_209 = lean_ctor_get(x_104, 0);
x_210 = lean_ctor_get(x_104, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_104);
x_211 = lean_ctor_get(x_209, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_213 = x_209;
} else {
 lean_dec_ref(x_209);
 x_213 = lean_box(0);
}
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_224; lean_object* x_225; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_213)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_213;
}
lean_ctor_set(x_224, 0, x_103);
lean_ctor_set(x_224, 1, x_212);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_210);
return x_225;
}
else
{
lean_object* x_226; uint8_t x_227; 
x_226 = lean_ctor_get(x_211, 0);
lean_inc(x_226);
lean_dec(x_211);
x_227 = lean_unbox(x_226);
lean_dec(x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_228 = lean_box(0);
x_229 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0;
if (lean_is_scalar(x_213)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_213;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_212);
x_37 = x_230;
x_38 = x_228;
x_39 = x_210;
goto block_93;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_213);
x_231 = lean_ctor_get(x_2, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_2, 1);
lean_inc(x_232);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_233 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_231, x_3, x_212, x_5, x_6, x_7, x_8, x_210);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
if (lean_obj_tag(x_235) == 0)
{
lean_dec(x_234);
lean_dec(x_232);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_233;
goto block_99;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_235);
x_236 = lean_ctor_get(x_233, 1);
lean_inc(x_236);
lean_dec(x_233);
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
lean_dec(x_234);
x_238 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_232, x_3, x_237, x_5, x_6, x_7, x_8, x_236);
x_94 = x_238;
goto block_99;
}
}
else
{
lean_dec(x_232);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_233;
goto block_99;
}
}
case 6:
{
lean_object* x_239; lean_object* x_240; 
lean_dec(x_213);
x_239 = lean_ctor_get(x_2, 1);
lean_inc(x_239);
x_240 = lean_ctor_get(x_2, 2);
lean_inc(x_240);
x_214 = x_239;
x_215 = x_240;
x_216 = x_3;
goto block_223;
}
case 7:
{
lean_object* x_241; lean_object* x_242; 
lean_dec(x_213);
x_241 = lean_ctor_get(x_2, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_2, 2);
lean_inc(x_242);
x_214 = x_241;
x_215 = x_242;
x_216 = x_3;
goto block_223;
}
case 8:
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_213);
x_243 = lean_ctor_get(x_2, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_2, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_2, 3);
lean_inc(x_245);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_246 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_243, x_3, x_212, x_5, x_6, x_7, x_8, x_210);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_dec(x_247);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_246;
goto block_99;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_248);
x_249 = lean_ctor_get(x_246, 1);
lean_inc(x_249);
lean_dec(x_246);
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_250);
lean_dec(x_247);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_251 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_244, x_3, x_250, x_5, x_6, x_7, x_8, x_249);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
if (lean_obj_tag(x_253) == 0)
{
lean_dec(x_252);
lean_dec(x_245);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_251;
goto block_99;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_253);
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
lean_dec(x_251);
x_255 = lean_ctor_get(x_252, 1);
lean_inc(x_255);
lean_dec(x_252);
x_256 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_245, x_3, x_255, x_5, x_6, x_7, x_8, x_254);
x_94 = x_256;
goto block_99;
}
}
else
{
lean_dec(x_245);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_251;
goto block_99;
}
}
}
else
{
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_246;
goto block_99;
}
}
case 10:
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_213);
x_257 = lean_ctor_get(x_2, 1);
lean_inc(x_257);
x_258 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_257, x_3, x_212, x_5, x_6, x_7, x_8, x_210);
x_94 = x_258;
goto block_99;
}
case 11:
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_213);
x_259 = lean_ctor_get(x_2, 2);
lean_inc(x_259);
x_260 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_259, x_3, x_212, x_5, x_6, x_7, x_8, x_210);
x_94 = x_260;
goto block_99;
}
default: 
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_261 = lean_box(0);
x_262 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0;
if (lean_is_scalar(x_213)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_213;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_212);
x_37 = x_263;
x_38 = x_261;
x_39 = x_210;
goto block_93;
}
}
}
}
block_223:
{
lean_object* x_217; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_217 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_214, x_216, x_212, x_5, x_6, x_7, x_8, x_210);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
if (lean_obj_tag(x_219) == 0)
{
lean_dec(x_218);
lean_dec(x_215);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_217;
goto block_99;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_219);
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
lean_dec(x_217);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec(x_218);
x_222 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_215, x_216, x_221, x_5, x_6, x_7, x_8, x_220);
x_94 = x_222;
goto block_99;
}
}
else
{
lean_dec(x_215);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = x_217;
goto block_99;
}
}
}
}
else
{
uint8_t x_264; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_264 = !lean_is_exclusive(x_104);
if (x_264 == 0)
{
return x_104;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_104, 0);
x_266 = lean_ctor_get(x_104, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_104);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_21, 0, x_103);
return x_19;
}
block_93:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_st_ref_take(x_3, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; size_t x_49; lean_object* x_50; uint8_t x_51; 
x_44 = lean_ctor_get(x_41, 0);
x_45 = lean_ctor_get(x_41, 1);
x_46 = lean_array_get_size(x_45);
x_47 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_48 = lean_usize_sub(x_47, x_36);
x_49 = lean_usize_land(x_34, x_48);
x_50 = lean_array_uget(x_45, x_49);
x_51 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_2, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_44, x_52);
lean_dec(x_44);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_2);
lean_ctor_set(x_54, 1, x_38);
lean_ctor_set(x_54, 2, x_50);
x_55 = lean_array_uset(x_45, x_49, x_54);
x_56 = lean_unsigned_to_nat(4u);
x_57 = lean_nat_mul(x_53, x_56);
x_58 = lean_unsigned_to_nat(3u);
x_59 = lean_nat_div(x_57, x_58);
lean_dec(x_57);
x_60 = lean_array_get_size(x_55);
x_61 = lean_nat_dec_le(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_55);
lean_ctor_set(x_41, 1, x_62);
lean_ctor_set(x_41, 0, x_53);
x_10 = x_37;
x_11 = x_42;
x_12 = x_41;
goto block_18;
}
else
{
lean_ctor_set(x_41, 1, x_55);
lean_ctor_set(x_41, 0, x_53);
x_10 = x_37;
x_11 = x_42;
x_12 = x_41;
goto block_18;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_array_uset(x_45, x_49, x_63);
x_65 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_2, x_38, x_50);
x_66 = lean_array_uset(x_64, x_49, x_65);
lean_ctor_set(x_41, 1, x_66);
x_10 = x_37;
x_11 = x_42;
x_12 = x_41;
goto block_18;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; size_t x_72; lean_object* x_73; uint8_t x_74; 
x_67 = lean_ctor_get(x_41, 0);
x_68 = lean_ctor_get(x_41, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_41);
x_69 = lean_array_get_size(x_68);
x_70 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_71 = lean_usize_sub(x_70, x_36);
x_72 = lean_usize_land(x_34, x_71);
x_73 = lean_array_uget(x_68, x_72);
x_74 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_2, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_67, x_75);
lean_dec(x_67);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_2);
lean_ctor_set(x_77, 1, x_38);
lean_ctor_set(x_77, 2, x_73);
x_78 = lean_array_uset(x_68, x_72, x_77);
x_79 = lean_unsigned_to_nat(4u);
x_80 = lean_nat_mul(x_76, x_79);
x_81 = lean_unsigned_to_nat(3u);
x_82 = lean_nat_div(x_80, x_81);
lean_dec(x_80);
x_83 = lean_array_get_size(x_78);
x_84 = lean_nat_dec_le(x_82, x_83);
lean_dec(x_83);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_78);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_76);
lean_ctor_set(x_86, 1, x_85);
x_10 = x_37;
x_11 = x_42;
x_12 = x_86;
goto block_18;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_76);
lean_ctor_set(x_87, 1, x_78);
x_10 = x_37;
x_11 = x_42;
x_12 = x_87;
goto block_18;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_box(0);
x_89 = lean_array_uset(x_68, x_72, x_88);
x_90 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_2, x_38, x_73);
x_91 = lean_array_uset(x_89, x_72, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_67);
lean_ctor_set(x_92, 1, x_91);
x_10 = x_37;
x_11 = x_42;
x_12 = x_92;
goto block_18;
}
}
}
block_99:
{
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
lean_dec(x_95);
lean_dec(x_2);
return x_94;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_37 = x_95;
x_38 = x_98;
x_39 = x_97;
goto block_93;
}
}
else
{
lean_dec(x_2);
return x_94;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; uint64_t x_271; uint64_t x_272; uint64_t x_273; uint64_t x_274; uint64_t x_275; uint64_t x_276; uint64_t x_277; size_t x_278; size_t x_279; size_t x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_315; size_t x_321; size_t x_322; lean_object* x_323; lean_object* x_324; 
x_268 = lean_ctor_get(x_19, 1);
x_269 = lean_ctor_get(x_21, 1);
lean_inc(x_269);
lean_dec(x_21);
x_270 = lean_array_get_size(x_269);
x_271 = l_Lean_Expr_hash(x_2);
x_272 = 32;
x_273 = lean_uint64_shift_right(x_271, x_272);
x_274 = lean_uint64_xor(x_271, x_273);
x_275 = 16;
x_276 = lean_uint64_shift_right(x_274, x_275);
x_277 = lean_uint64_xor(x_274, x_276);
x_278 = lean_uint64_to_usize(x_277);
x_279 = lean_usize_of_nat(x_270);
lean_dec(x_270);
x_280 = 1;
x_321 = lean_usize_sub(x_279, x_280);
x_322 = lean_usize_land(x_278, x_321);
x_323 = lean_array_uget(x_269, x_322);
lean_dec(x_269);
x_324 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0___redArg(x_2, x_323);
lean_dec(x_323);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; 
lean_free_object(x_19);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_325 = lean_apply_7(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_268);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
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
x_329 = lean_ctor_get(x_326, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_326, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_331 = x_326;
} else {
 lean_dec_ref(x_326);
 x_331 = lean_box(0);
}
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_342; lean_object* x_343; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_331)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_331;
}
lean_ctor_set(x_342, 0, x_324);
lean_ctor_set(x_342, 1, x_330);
if (lean_is_scalar(x_328)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_328;
}
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_327);
return x_343;
}
else
{
lean_object* x_344; uint8_t x_345; 
lean_dec(x_328);
x_344 = lean_ctor_get(x_329, 0);
lean_inc(x_344);
lean_dec(x_329);
x_345 = lean_unbox(x_344);
lean_dec(x_344);
if (x_345 == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_346 = lean_box(0);
x_347 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0;
if (lean_is_scalar(x_331)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_331;
}
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_330);
x_281 = x_348;
x_282 = x_346;
x_283 = x_327;
goto block_314;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_331);
x_349 = lean_ctor_get(x_2, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_2, 1);
lean_inc(x_350);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_351 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_349, x_3, x_330, x_5, x_6, x_7, x_8, x_327);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
if (lean_obj_tag(x_353) == 0)
{
lean_dec(x_352);
lean_dec(x_350);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_315 = x_351;
goto block_320;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_353);
x_354 = lean_ctor_get(x_351, 1);
lean_inc(x_354);
lean_dec(x_351);
x_355 = lean_ctor_get(x_352, 1);
lean_inc(x_355);
lean_dec(x_352);
x_356 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_350, x_3, x_355, x_5, x_6, x_7, x_8, x_354);
x_315 = x_356;
goto block_320;
}
}
else
{
lean_dec(x_350);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_315 = x_351;
goto block_320;
}
}
case 6:
{
lean_object* x_357; lean_object* x_358; 
lean_dec(x_331);
x_357 = lean_ctor_get(x_2, 1);
lean_inc(x_357);
x_358 = lean_ctor_get(x_2, 2);
lean_inc(x_358);
x_332 = x_357;
x_333 = x_358;
x_334 = x_3;
goto block_341;
}
case 7:
{
lean_object* x_359; lean_object* x_360; 
lean_dec(x_331);
x_359 = lean_ctor_get(x_2, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_2, 2);
lean_inc(x_360);
x_332 = x_359;
x_333 = x_360;
x_334 = x_3;
goto block_341;
}
case 8:
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_331);
x_361 = lean_ctor_get(x_2, 1);
lean_inc(x_361);
x_362 = lean_ctor_get(x_2, 2);
lean_inc(x_362);
x_363 = lean_ctor_get(x_2, 3);
lean_inc(x_363);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_364 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_361, x_3, x_330, x_5, x_6, x_7, x_8, x_327);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
if (lean_obj_tag(x_366) == 0)
{
lean_dec(x_365);
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_315 = x_364;
goto block_320;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_366);
x_367 = lean_ctor_get(x_364, 1);
lean_inc(x_367);
lean_dec(x_364);
x_368 = lean_ctor_get(x_365, 1);
lean_inc(x_368);
lean_dec(x_365);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_369 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_362, x_3, x_368, x_5, x_6, x_7, x_8, x_367);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
if (lean_obj_tag(x_371) == 0)
{
lean_dec(x_370);
lean_dec(x_363);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_315 = x_369;
goto block_320;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_371);
x_372 = lean_ctor_get(x_369, 1);
lean_inc(x_372);
lean_dec(x_369);
x_373 = lean_ctor_get(x_370, 1);
lean_inc(x_373);
lean_dec(x_370);
x_374 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_363, x_3, x_373, x_5, x_6, x_7, x_8, x_372);
x_315 = x_374;
goto block_320;
}
}
else
{
lean_dec(x_363);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_315 = x_369;
goto block_320;
}
}
}
else
{
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_315 = x_364;
goto block_320;
}
}
case 10:
{
lean_object* x_375; lean_object* x_376; 
lean_dec(x_331);
x_375 = lean_ctor_get(x_2, 1);
lean_inc(x_375);
x_376 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_375, x_3, x_330, x_5, x_6, x_7, x_8, x_327);
x_315 = x_376;
goto block_320;
}
case 11:
{
lean_object* x_377; lean_object* x_378; 
lean_dec(x_331);
x_377 = lean_ctor_get(x_2, 2);
lean_inc(x_377);
x_378 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_377, x_3, x_330, x_5, x_6, x_7, x_8, x_327);
x_315 = x_378;
goto block_320;
}
default: 
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_379 = lean_box(0);
x_380 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0;
if (lean_is_scalar(x_331)) {
 x_381 = lean_alloc_ctor(0, 2, 0);
} else {
 x_381 = x_331;
}
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_330);
x_281 = x_381;
x_282 = x_379;
x_283 = x_327;
goto block_314;
}
}
}
}
block_341:
{
lean_object* x_335; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_335 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_332, x_334, x_330, x_5, x_6, x_7, x_8, x_327);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
if (lean_obj_tag(x_337) == 0)
{
lean_dec(x_336);
lean_dec(x_333);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_315 = x_335;
goto block_320;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_337);
x_338 = lean_ctor_get(x_335, 1);
lean_inc(x_338);
lean_dec(x_335);
x_339 = lean_ctor_get(x_336, 1);
lean_inc(x_339);
lean_dec(x_336);
x_340 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_333, x_334, x_339, x_5, x_6, x_7, x_8, x_338);
x_315 = x_340;
goto block_320;
}
}
else
{
lean_dec(x_333);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_315 = x_335;
goto block_320;
}
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_382 = lean_ctor_get(x_325, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_325, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_384 = x_325;
} else {
 lean_dec_ref(x_325);
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
else
{
lean_object* x_386; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_386, 0, x_324);
lean_ctor_set(x_386, 1, x_4);
lean_ctor_set(x_19, 0, x_386);
return x_19;
}
block_314:
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; size_t x_291; size_t x_292; size_t x_293; lean_object* x_294; uint8_t x_295; 
x_284 = lean_st_ref_take(x_3, x_283);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_287 = lean_ctor_get(x_285, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_285, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_289 = x_285;
} else {
 lean_dec_ref(x_285);
 x_289 = lean_box(0);
}
x_290 = lean_array_get_size(x_288);
x_291 = lean_usize_of_nat(x_290);
lean_dec(x_290);
x_292 = lean_usize_sub(x_291, x_280);
x_293 = lean_usize_land(x_278, x_292);
x_294 = lean_array_uget(x_288, x_293);
x_295 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_2, x_294);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_296 = lean_unsigned_to_nat(1u);
x_297 = lean_nat_add(x_287, x_296);
lean_dec(x_287);
x_298 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_298, 0, x_2);
lean_ctor_set(x_298, 1, x_282);
lean_ctor_set(x_298, 2, x_294);
x_299 = lean_array_uset(x_288, x_293, x_298);
x_300 = lean_unsigned_to_nat(4u);
x_301 = lean_nat_mul(x_297, x_300);
x_302 = lean_unsigned_to_nat(3u);
x_303 = lean_nat_div(x_301, x_302);
lean_dec(x_301);
x_304 = lean_array_get_size(x_299);
x_305 = lean_nat_dec_le(x_303, x_304);
lean_dec(x_304);
lean_dec(x_303);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; 
x_306 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_299);
if (lean_is_scalar(x_289)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_289;
}
lean_ctor_set(x_307, 0, x_297);
lean_ctor_set(x_307, 1, x_306);
x_10 = x_281;
x_11 = x_286;
x_12 = x_307;
goto block_18;
}
else
{
lean_object* x_308; 
if (lean_is_scalar(x_289)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_289;
}
lean_ctor_set(x_308, 0, x_297);
lean_ctor_set(x_308, 1, x_299);
x_10 = x_281;
x_11 = x_286;
x_12 = x_308;
goto block_18;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_309 = lean_box(0);
x_310 = lean_array_uset(x_288, x_293, x_309);
x_311 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_2, x_282, x_294);
x_312 = lean_array_uset(x_310, x_293, x_311);
if (lean_is_scalar(x_289)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_289;
}
lean_ctor_set(x_313, 0, x_287);
lean_ctor_set(x_313, 1, x_312);
x_10 = x_281;
x_11 = x_286;
x_12 = x_313;
goto block_18;
}
}
block_320:
{
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
if (lean_obj_tag(x_317) == 0)
{
lean_dec(x_316);
lean_dec(x_2);
return x_315;
}
else
{
lean_object* x_318; lean_object* x_319; 
x_318 = lean_ctor_get(x_315, 1);
lean_inc(x_318);
lean_dec(x_315);
x_319 = lean_ctor_get(x_317, 0);
lean_inc(x_319);
lean_dec(x_317);
x_281 = x_316;
x_282 = x_319;
x_283 = x_318;
goto block_314;
}
}
else
{
lean_dec(x_2);
return x_315;
}
}
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint64_t x_392; uint64_t x_393; uint64_t x_394; uint64_t x_395; uint64_t x_396; uint64_t x_397; uint64_t x_398; size_t x_399; size_t x_400; size_t x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_436; size_t x_442; size_t x_443; lean_object* x_444; lean_object* x_445; 
x_387 = lean_ctor_get(x_19, 0);
x_388 = lean_ctor_get(x_19, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_19);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_390 = x_387;
} else {
 lean_dec_ref(x_387);
 x_390 = lean_box(0);
}
x_391 = lean_array_get_size(x_389);
x_392 = l_Lean_Expr_hash(x_2);
x_393 = 32;
x_394 = lean_uint64_shift_right(x_392, x_393);
x_395 = lean_uint64_xor(x_392, x_394);
x_396 = 16;
x_397 = lean_uint64_shift_right(x_395, x_396);
x_398 = lean_uint64_xor(x_395, x_397);
x_399 = lean_uint64_to_usize(x_398);
x_400 = lean_usize_of_nat(x_391);
lean_dec(x_391);
x_401 = 1;
x_442 = lean_usize_sub(x_400, x_401);
x_443 = lean_usize_land(x_399, x_442);
x_444 = lean_array_uget(x_389, x_443);
lean_dec(x_389);
x_445 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0___redArg(x_2, x_444);
lean_dec(x_444);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; 
lean_dec(x_390);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_446 = lean_apply_7(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_388);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_446, 1);
lean_inc(x_448);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 x_449 = x_446;
} else {
 lean_dec_ref(x_446);
 x_449 = lean_box(0);
}
x_450 = lean_ctor_get(x_447, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_447, 1);
lean_inc(x_451);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_452 = x_447;
} else {
 lean_dec_ref(x_447);
 x_452 = lean_box(0);
}
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_463; lean_object* x_464; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_452)) {
 x_463 = lean_alloc_ctor(0, 2, 0);
} else {
 x_463 = x_452;
}
lean_ctor_set(x_463, 0, x_445);
lean_ctor_set(x_463, 1, x_451);
if (lean_is_scalar(x_449)) {
 x_464 = lean_alloc_ctor(0, 2, 0);
} else {
 x_464 = x_449;
}
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_448);
return x_464;
}
else
{
lean_object* x_465; uint8_t x_466; 
lean_dec(x_449);
x_465 = lean_ctor_get(x_450, 0);
lean_inc(x_465);
lean_dec(x_450);
x_466 = lean_unbox(x_465);
lean_dec(x_465);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_467 = lean_box(0);
x_468 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0;
if (lean_is_scalar(x_452)) {
 x_469 = lean_alloc_ctor(0, 2, 0);
} else {
 x_469 = x_452;
}
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_469, 1, x_451);
x_402 = x_469;
x_403 = x_467;
x_404 = x_448;
goto block_435;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_452);
x_470 = lean_ctor_get(x_2, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_2, 1);
lean_inc(x_471);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_472 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_470, x_3, x_451, x_5, x_6, x_7, x_8, x_448);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
if (lean_obj_tag(x_474) == 0)
{
lean_dec(x_473);
lean_dec(x_471);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_436 = x_472;
goto block_441;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
lean_dec(x_474);
x_475 = lean_ctor_get(x_472, 1);
lean_inc(x_475);
lean_dec(x_472);
x_476 = lean_ctor_get(x_473, 1);
lean_inc(x_476);
lean_dec(x_473);
x_477 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_471, x_3, x_476, x_5, x_6, x_7, x_8, x_475);
x_436 = x_477;
goto block_441;
}
}
else
{
lean_dec(x_471);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_436 = x_472;
goto block_441;
}
}
case 6:
{
lean_object* x_478; lean_object* x_479; 
lean_dec(x_452);
x_478 = lean_ctor_get(x_2, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_2, 2);
lean_inc(x_479);
x_453 = x_478;
x_454 = x_479;
x_455 = x_3;
goto block_462;
}
case 7:
{
lean_object* x_480; lean_object* x_481; 
lean_dec(x_452);
x_480 = lean_ctor_get(x_2, 1);
lean_inc(x_480);
x_481 = lean_ctor_get(x_2, 2);
lean_inc(x_481);
x_453 = x_480;
x_454 = x_481;
x_455 = x_3;
goto block_462;
}
case 8:
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
lean_dec(x_452);
x_482 = lean_ctor_get(x_2, 1);
lean_inc(x_482);
x_483 = lean_ctor_get(x_2, 2);
lean_inc(x_483);
x_484 = lean_ctor_get(x_2, 3);
lean_inc(x_484);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_485 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_482, x_3, x_451, x_5, x_6, x_7, x_8, x_448);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; lean_object* x_487; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
if (lean_obj_tag(x_487) == 0)
{
lean_dec(x_486);
lean_dec(x_484);
lean_dec(x_483);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_436 = x_485;
goto block_441;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec(x_487);
x_488 = lean_ctor_get(x_485, 1);
lean_inc(x_488);
lean_dec(x_485);
x_489 = lean_ctor_get(x_486, 1);
lean_inc(x_489);
lean_dec(x_486);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_490 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_483, x_3, x_489, x_5, x_6, x_7, x_8, x_488);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
if (lean_obj_tag(x_492) == 0)
{
lean_dec(x_491);
lean_dec(x_484);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_436 = x_490;
goto block_441;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec(x_492);
x_493 = lean_ctor_get(x_490, 1);
lean_inc(x_493);
lean_dec(x_490);
x_494 = lean_ctor_get(x_491, 1);
lean_inc(x_494);
lean_dec(x_491);
x_495 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_484, x_3, x_494, x_5, x_6, x_7, x_8, x_493);
x_436 = x_495;
goto block_441;
}
}
else
{
lean_dec(x_484);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_436 = x_490;
goto block_441;
}
}
}
else
{
lean_dec(x_484);
lean_dec(x_483);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_436 = x_485;
goto block_441;
}
}
case 10:
{
lean_object* x_496; lean_object* x_497; 
lean_dec(x_452);
x_496 = lean_ctor_get(x_2, 1);
lean_inc(x_496);
x_497 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_496, x_3, x_451, x_5, x_6, x_7, x_8, x_448);
x_436 = x_497;
goto block_441;
}
case 11:
{
lean_object* x_498; lean_object* x_499; 
lean_dec(x_452);
x_498 = lean_ctor_get(x_2, 2);
lean_inc(x_498);
x_499 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_498, x_3, x_451, x_5, x_6, x_7, x_8, x_448);
x_436 = x_499;
goto block_441;
}
default: 
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_500 = lean_box(0);
x_501 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0;
if (lean_is_scalar(x_452)) {
 x_502 = lean_alloc_ctor(0, 2, 0);
} else {
 x_502 = x_452;
}
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_451);
x_402 = x_502;
x_403 = x_500;
x_404 = x_448;
goto block_435;
}
}
}
}
block_462:
{
lean_object* x_456; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_456 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_453, x_455, x_451, x_5, x_6, x_7, x_8, x_448);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
if (lean_obj_tag(x_458) == 0)
{
lean_dec(x_457);
lean_dec(x_454);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_436 = x_456;
goto block_441;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_458);
x_459 = lean_ctor_get(x_456, 1);
lean_inc(x_459);
lean_dec(x_456);
x_460 = lean_ctor_get(x_457, 1);
lean_inc(x_460);
lean_dec(x_457);
x_461 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_454, x_455, x_460, x_5, x_6, x_7, x_8, x_459);
x_436 = x_461;
goto block_441;
}
}
else
{
lean_dec(x_454);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_436 = x_456;
goto block_441;
}
}
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_503 = lean_ctor_get(x_446, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_446, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 x_505 = x_446;
} else {
 lean_dec_ref(x_446);
 x_505 = lean_box(0);
}
if (lean_is_scalar(x_505)) {
 x_506 = lean_alloc_ctor(1, 2, 0);
} else {
 x_506 = x_505;
}
lean_ctor_set(x_506, 0, x_503);
lean_ctor_set(x_506, 1, x_504);
return x_506;
}
}
else
{
lean_object* x_507; lean_object* x_508; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_390)) {
 x_507 = lean_alloc_ctor(0, 2, 0);
} else {
 x_507 = x_390;
}
lean_ctor_set(x_507, 0, x_445);
lean_ctor_set(x_507, 1, x_4);
x_508 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_508, 0, x_507);
lean_ctor_set(x_508, 1, x_388);
return x_508;
}
block_435:
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; size_t x_412; size_t x_413; size_t x_414; lean_object* x_415; uint8_t x_416; 
x_405 = lean_st_ref_take(x_3, x_404);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
x_408 = lean_ctor_get(x_406, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_406, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 x_410 = x_406;
} else {
 lean_dec_ref(x_406);
 x_410 = lean_box(0);
}
x_411 = lean_array_get_size(x_409);
x_412 = lean_usize_of_nat(x_411);
lean_dec(x_411);
x_413 = lean_usize_sub(x_412, x_401);
x_414 = lean_usize_land(x_399, x_413);
x_415 = lean_array_uget(x_409, x_414);
x_416 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_2, x_415);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; 
x_417 = lean_unsigned_to_nat(1u);
x_418 = lean_nat_add(x_408, x_417);
lean_dec(x_408);
x_419 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_419, 0, x_2);
lean_ctor_set(x_419, 1, x_403);
lean_ctor_set(x_419, 2, x_415);
x_420 = lean_array_uset(x_409, x_414, x_419);
x_421 = lean_unsigned_to_nat(4u);
x_422 = lean_nat_mul(x_418, x_421);
x_423 = lean_unsigned_to_nat(3u);
x_424 = lean_nat_div(x_422, x_423);
lean_dec(x_422);
x_425 = lean_array_get_size(x_420);
x_426 = lean_nat_dec_le(x_424, x_425);
lean_dec(x_425);
lean_dec(x_424);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; 
x_427 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_420);
if (lean_is_scalar(x_410)) {
 x_428 = lean_alloc_ctor(0, 2, 0);
} else {
 x_428 = x_410;
}
lean_ctor_set(x_428, 0, x_418);
lean_ctor_set(x_428, 1, x_427);
x_10 = x_402;
x_11 = x_407;
x_12 = x_428;
goto block_18;
}
else
{
lean_object* x_429; 
if (lean_is_scalar(x_410)) {
 x_429 = lean_alloc_ctor(0, 2, 0);
} else {
 x_429 = x_410;
}
lean_ctor_set(x_429, 0, x_418);
lean_ctor_set(x_429, 1, x_420);
x_10 = x_402;
x_11 = x_407;
x_12 = x_429;
goto block_18;
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_430 = lean_box(0);
x_431 = lean_array_uset(x_409, x_414, x_430);
x_432 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_2, x_403, x_415);
x_433 = lean_array_uset(x_431, x_414, x_432);
if (lean_is_scalar(x_410)) {
 x_434 = lean_alloc_ctor(0, 2, 0);
} else {
 x_434 = x_410;
}
lean_ctor_set(x_434, 0, x_408);
lean_ctor_set(x_434, 1, x_433);
x_10 = x_402;
x_11 = x_407;
x_12 = x_434;
goto block_18;
}
}
block_441:
{
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
if (lean_obj_tag(x_438) == 0)
{
lean_dec(x_437);
lean_dec(x_2);
return x_436;
}
else
{
lean_object* x_439; lean_object* x_440; 
x_439 = lean_ctor_get(x_436, 1);
lean_inc(x_439);
lean_dec(x_436);
x_440 = lean_ctor_get(x_438, 0);
lean_inc(x_440);
lean_dec(x_438);
x_402 = x_437;
x_403 = x_440;
x_404 = x_439;
goto block_435;
}
}
else
{
lean_dec(x_2);
return x_436;
}
}
}
block_18:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_ref_set(x_3, x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_10);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_9 = l_Lean_Expr_hasExprMVar(x_2);
if (x_9 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_box(x_9);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_8);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = l_Lean_Expr_isMVar(x_2);
if (x_46 == 0)
{
x_17 = x_46;
goto block_41;
}
else
{
uint8_t x_47; 
x_47 = l_Array_contains___at___Lean_Meta_arrowDomainsN_spec__0(x_1, x_2);
x_17 = x_47;
goto block_41;
}
}
block_16:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_box(x_9);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
block_41:
{
if (x_17 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = x_3;
x_11 = x_8;
goto block_16;
}
else
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_19, 0, x_25);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_31 = x_19;
} else {
 lean_dec_ref(x_19);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_20);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_dec(x_19);
x_10 = x_36;
x_11 = x_35;
goto block_16;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = lean_infer_type(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__0___redArg(x_10, x_3, x_5, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__4;
x_19 = lean_st_mk_ref(x_18, x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___lam__0), 8, 1);
lean_closure_set(x_22, 0, x_1);
x_23 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_22, x_17, x_20, x_16, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_dec(x_24);
lean_dec(x_20);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_st_ref_get(x_20, x_26);
lean_dec(x_20);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_24);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_dec(x_20);
return x_23;
}
}
else
{
uint8_t x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
return x_9;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_9, 0);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_9);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_17 = lean_array_uget(x_3, x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_18 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit(x_1, x_17, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
lean_dec(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
lean_inc(x_2);
{
size_t _tmp_4 = x_24;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_6 = x_22;
lean_object* _tmp_11 = x_21;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_12 = _tmp_11;
}
goto _start;
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = lean_array_size(x_1);
x_10 = 0;
lean_inc(x_1);
x_11 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go_spec__0(x_1, x_8, x_1, x_9, x_10, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_12);
return x_11;
}
else
{
uint8_t x_14; 
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0;
lean_ctor_set(x_12, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_24 = x_12;
} else {
 lean_dec_ref(x_12);
 x_24 = lean_box(0);
}
x_25 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0;
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
}
else
{
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go_spec__0(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0;
x_2 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__4;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__1;
x_8 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_8, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_19, 2);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_10, 0, x_22);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_dec(x_8);
x_24 = lean_ctor_get(x_19, 2);
lean_inc(x_24);
lean_dec(x_19);
lean_ctor_set(x_10, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_10);
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_dec(x_9);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_28 = x_8;
} else {
 lean_dec_ref(x_8);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_26, 2);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_8);
if (x_32 == 0)
{
return x_8;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_8, 0);
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_8);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_19);
x_20 = lean_infer_type(x_19, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_21, x_7, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_32; uint8_t x_33; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_28 = x_5;
} else {
 lean_dec_ref(x_5);
 x_28 = lean_box(0);
}
x_32 = l_Lean_Expr_cleanupAnnotations(x_25);
x_33 = l_Lean_Expr_isApp(x_32);
if (x_33 == 0)
{
lean_dec(x_32);
lean_free_object(x_23);
lean_dec(x_19);
x_29 = x_26;
goto block_31;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
x_35 = l_Lean_Expr_appFnCleanup___redArg(x_32);
x_36 = l_Lean_Expr_isApp(x_35);
if (x_36 == 0)
{
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_23);
lean_dec(x_19);
x_29 = x_26;
goto block_31;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
x_38 = l_Lean_Expr_appFnCleanup___redArg(x_35);
x_39 = l_Lean_Expr_isApp(x_38);
if (x_39 == 0)
{
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_34);
lean_free_object(x_23);
lean_dec(x_19);
x_29 = x_26;
goto block_31;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = l_Lean_Expr_appFnCleanup___redArg(x_38);
x_41 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__1;
x_42 = l_Lean_Expr_isConstOf(x_40, x_41);
lean_dec(x_40);
if (x_42 == 0)
{
lean_dec(x_37);
lean_dec(x_34);
lean_free_object(x_23);
lean_dec(x_19);
x_29 = x_26;
goto block_31;
}
else
{
lean_object* x_43; 
lean_dec(x_28);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_37);
x_43 = l_Lean_Meta_isExprDefEq(x_37, x_34, x_6, x_7, x_8, x_9, x_26);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_37);
lean_dec(x_19);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
lean_inc(x_1);
lean_ctor_set(x_23, 1, x_27);
lean_ctor_set(x_23, 0, x_1);
x_11 = x_23;
x_12 = x_46;
goto block_16;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_48 = l_Lean_Meta_mkEqRefl(x_37, x_6, x_7, x_8, x_9, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Expr_mvarId_x21(x_19);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_52 = lean_checked_assign(x_51, x_49, x_6, x_7, x_8, x_9, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_52, 0);
lean_dec(x_56);
x_57 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__2;
lean_ctor_set(x_23, 1, x_27);
lean_ctor_set(x_23, 0, x_57);
lean_ctor_set(x_52, 0, x_23);
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_dec(x_52);
x_59 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__2;
lean_ctor_set(x_23, 1, x_27);
lean_ctor_set(x_23, 0, x_59);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_23);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_27);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_dec(x_52);
x_62 = lean_box(x_42);
lean_inc(x_1);
lean_ctor_set(x_23, 1, x_62);
lean_ctor_set(x_23, 0, x_1);
x_11 = x_23;
x_12 = x_61;
goto block_16;
}
}
else
{
uint8_t x_63; 
lean_dec(x_27);
lean_free_object(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_52);
if (x_63 == 0)
{
return x_52;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_52, 0);
x_65 = lean_ctor_get(x_52, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_52);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_27);
lean_free_object(x_23);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_48);
if (x_67 == 0)
{
return x_48;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_48, 0);
x_69 = lean_ctor_get(x_48, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_48);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_37);
lean_dec(x_27);
lean_free_object(x_23);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_43);
if (x_71 == 0)
{
return x_43;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_43, 0);
x_73 = lean_ctor_get(x_43, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_43);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
}
block_31:
{
lean_object* x_30; 
lean_inc(x_1);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_27);
x_11 = x_30;
x_12 = x_29;
goto block_16;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_82; uint8_t x_83; 
x_75 = lean_ctor_get(x_23, 0);
x_76 = lean_ctor_get(x_23, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_23);
x_77 = lean_ctor_get(x_5, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_78 = x_5;
} else {
 lean_dec_ref(x_5);
 x_78 = lean_box(0);
}
x_82 = l_Lean_Expr_cleanupAnnotations(x_75);
x_83 = l_Lean_Expr_isApp(x_82);
if (x_83 == 0)
{
lean_dec(x_82);
lean_dec(x_19);
x_79 = x_76;
goto block_81;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
x_85 = l_Lean_Expr_appFnCleanup___redArg(x_82);
x_86 = l_Lean_Expr_isApp(x_85);
if (x_86 == 0)
{
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_19);
x_79 = x_76;
goto block_81;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
x_88 = l_Lean_Expr_appFnCleanup___redArg(x_85);
x_89 = l_Lean_Expr_isApp(x_88);
if (x_89 == 0)
{
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_84);
lean_dec(x_19);
x_79 = x_76;
goto block_81;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = l_Lean_Expr_appFnCleanup___redArg(x_88);
x_91 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__1;
x_92 = l_Lean_Expr_isConstOf(x_90, x_91);
lean_dec(x_90);
if (x_92 == 0)
{
lean_dec(x_87);
lean_dec(x_84);
lean_dec(x_19);
x_79 = x_76;
goto block_81;
}
else
{
lean_object* x_93; 
lean_dec(x_78);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_87);
x_93 = l_Lean_Meta_isExprDefEq(x_87, x_84, x_6, x_7, x_8, x_9, x_76);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_87);
lean_dec(x_19);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
lean_inc(x_1);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_1);
lean_ctor_set(x_97, 1, x_77);
x_11 = x_97;
x_12 = x_96;
goto block_16;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
lean_dec(x_93);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_99 = l_Lean_Meta_mkEqRefl(x_87, x_6, x_7, x_8, x_9, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_Expr_mvarId_x21(x_19);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_103 = lean_checked_assign(x_102, x_100, x_6, x_7, x_8, x_9, x_101);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_107 = x_103;
} else {
 lean_dec_ref(x_103);
 x_107 = lean_box(0);
}
x_108 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__2;
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_77);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_106);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_77);
x_111 = lean_ctor_get(x_103, 1);
lean_inc(x_111);
lean_dec(x_103);
x_112 = lean_box(x_92);
lean_inc(x_1);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_1);
lean_ctor_set(x_113, 1, x_112);
x_11 = x_113;
x_12 = x_111;
goto block_16;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_77);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_114 = lean_ctor_get(x_103, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_103, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_116 = x_103;
} else {
 lean_dec_ref(x_103);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_77);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_118 = lean_ctor_get(x_99, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_99, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_120 = x_99;
} else {
 lean_dec_ref(x_99);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_87);
lean_dec(x_77);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_122 = lean_ctor_get(x_93, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_93, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_124 = x_93;
} else {
 lean_dec_ref(x_93);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
}
}
}
block_81:
{
lean_object* x_80; 
lean_inc(x_1);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_77);
x_11 = x_80;
x_12 = x_79;
goto block_16;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_20);
if (x_126 == 0)
{
return x_20;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_20, 0);
x_128 = lean_ctor_get(x_20, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_20);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_array_uget(x_1, x_2);
x_18 = l_Lean_Expr_mvarId_x21(x_14);
x_19 = l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0___redArg(x_18, x_5, x_6);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_15 = x_22;
goto block_17;
}
else
{
lean_object* x_23; 
lean_dec(x_14);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_7 = x_4;
x_8 = x_23;
goto block_12;
}
block_17:
{
lean_object* x_16; 
x_16 = lean_array_push(x_4, x_14);
x_7 = x_16;
x_8 = x_15;
goto block_12;
}
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_6);
return x_24;
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___redArg(x_1, x_2, x_3, x_4, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = l_Lean_Expr_mvarId_x21(x_7);
lean_dec(x_7);
x_9 = l_Lean_MVarId_isDelayedAssigned___at___Lean_Meta_getMVarsNoDelayed_spec__0___redArg(x_8, x_4, x_5);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_5 = x_12;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___redArg(x_1, x_2, x_3, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_14 = x_10;
} else {
 lean_dec_ref(x_10);
 x_14 = lean_box(0);
}
x_15 = l_Array_isEmpty___redArg(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
lean_free_object(x_8);
x_16 = lean_box(0);
x_17 = lean_box(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_size(x_12);
x_20 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_21 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0(x_16, x_12, x_19, x_20, x_18, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_97; 
x_97 = lean_unbox(x_26);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_24;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_23);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; uint8_t x_121; 
x_100 = lean_unsigned_to_nat(0u);
x_101 = lean_array_get_size(x_12);
x_121 = lean_nat_dec_lt(x_100, x_101);
if (x_121 == 0)
{
x_102 = x_15;
x_103 = x_23;
goto block_120;
}
else
{
if (x_121 == 0)
{
x_102 = x_15;
x_103 = x_23;
goto block_120;
}
else
{
size_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_122 = lean_usize_of_nat(x_101);
x_123 = l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___redArg(x_12, x_20, x_122, x_4, x_23);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_unbox(x_124);
lean_dec(x_124);
x_102 = x_126;
x_103 = x_125;
goto block_120;
}
}
block_120:
{
if (x_102 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_24);
x_104 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_13, x_4, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_mkAppN(x_2, x_12);
x_108 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_107, x_4, x_106);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0;
x_112 = lean_nat_dec_lt(x_100, x_101);
if (x_112 == 0)
{
lean_dec(x_101);
lean_dec(x_12);
x_27 = x_109;
x_28 = x_105;
x_29 = x_111;
x_30 = x_110;
goto block_96;
}
else
{
uint8_t x_113; 
x_113 = lean_nat_dec_le(x_101, x_101);
if (x_113 == 0)
{
lean_dec(x_101);
lean_dec(x_12);
x_27 = x_109;
x_28 = x_105;
x_29 = x_111;
x_30 = x_110;
goto block_96;
}
else
{
size_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_usize_of_nat(x_101);
lean_dec(x_101);
x_115 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___redArg(x_12, x_20, x_114, x_111, x_4, x_110);
lean_dec(x_12);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_27 = x_109;
x_28 = x_105;
x_29 = x_116;
x_30 = x_117;
goto block_96;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_101);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_118 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_24;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_103);
return x_119;
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_127 = lean_ctor_get(x_25, 0);
lean_inc(x_127);
lean_dec(x_25);
if (lean_is_scalar(x_24)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_24;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_23);
return x_128;
}
block_96:
{
lean_object* x_31; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_31 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f(x_29, x_3, x_4, x_5, x_6, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_box(0);
x_43 = lean_unbox(x_26);
x_44 = lean_unbox(x_42);
lean_inc(x_41);
x_45 = l_Lean_Meta_mkForallFVars(x_41, x_28, x_15, x_43, x_44, x_3, x_4, x_5, x_6, x_39);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_box(1);
x_49 = lean_unbox(x_26);
lean_dec(x_26);
x_50 = lean_unbox(x_48);
x_51 = l_Lean_Meta_mkLambdaFVars(x_41, x_27, x_15, x_49, x_15, x_50, x_3, x_4, x_5, x_6, x_47);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
if (lean_is_scalar(x_14)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_14;
}
lean_ctor_set(x_54, 0, x_46);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_32, 0, x_54);
lean_ctor_set(x_51, 0, x_32);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_51);
if (lean_is_scalar(x_14)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_14;
}
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_32, 0, x_57);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_32);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_46);
lean_free_object(x_32);
lean_dec(x_14);
x_59 = !lean_is_exclusive(x_51);
if (x_59 == 0)
{
return x_51;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_51, 0);
x_61 = lean_ctor_get(x_51, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_51);
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
lean_free_object(x_32);
lean_dec(x_41);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_45);
if (x_63 == 0)
{
return x_45;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_45, 0);
x_65 = lean_ctor_get(x_45, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_45);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_32, 0);
lean_inc(x_67);
lean_dec(x_32);
x_68 = lean_box(0);
x_69 = lean_unbox(x_26);
x_70 = lean_unbox(x_68);
lean_inc(x_67);
x_71 = l_Lean_Meta_mkForallFVars(x_67, x_28, x_15, x_69, x_70, x_3, x_4, x_5, x_6, x_39);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_box(1);
x_75 = lean_unbox(x_26);
lean_dec(x_26);
x_76 = lean_unbox(x_74);
x_77 = l_Lean_Meta_mkLambdaFVars(x_67, x_27, x_15, x_75, x_15, x_76, x_3, x_4, x_5, x_6, x_73);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_14)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_14;
}
lean_ctor_set(x_81, 0, x_72);
lean_ctor_set(x_81, 1, x_78);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
if (lean_is_scalar(x_80)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_80;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_79);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_72);
lean_dec(x_14);
x_84 = lean_ctor_get(x_77, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_77, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_86 = x_77;
} else {
 lean_dec_ref(x_77);
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
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_67);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_88 = lean_ctor_get(x_71, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_71, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_90 = x_71;
} else {
 lean_dec_ref(x_71);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_92 = !lean_is_exclusive(x_31);
if (x_92 == 0)
{
return x_31;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_31, 0);
x_94 = lean_ctor_get(x_31, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_31);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_21);
if (x_129 == 0)
{
return x_21;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_21, 0);
x_131 = lean_ctor_get(x_21, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_21);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
lean_object* x_133; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_133 = lean_box(0);
lean_ctor_set(x_8, 0, x_133);
return x_8;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_134 = lean_ctor_get(x_8, 0);
x_135 = lean_ctor_get(x_8, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_8);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_138 = x_134;
} else {
 lean_dec_ref(x_134);
 x_138 = lean_box(0);
}
x_139 = l_Array_isEmpty___redArg(x_136);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; size_t x_143; size_t x_144; lean_object* x_145; 
x_140 = lean_box(0);
x_141 = lean_box(x_139);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_array_size(x_136);
x_144 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_145 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0(x_140, x_136, x_143, x_144, x_142, x_3, x_4, x_5, x_6, x_135);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_146, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_146, 1);
lean_inc(x_150);
lean_dec(x_146);
if (lean_obj_tag(x_149) == 0)
{
uint8_t x_193; 
x_193 = lean_unbox(x_150);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_150);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_194 = lean_box(0);
if (lean_is_scalar(x_148)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_148;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_147);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; uint8_t x_217; 
x_196 = lean_unsigned_to_nat(0u);
x_197 = lean_array_get_size(x_136);
x_217 = lean_nat_dec_lt(x_196, x_197);
if (x_217 == 0)
{
x_198 = x_139;
x_199 = x_147;
goto block_216;
}
else
{
if (x_217 == 0)
{
x_198 = x_139;
x_199 = x_147;
goto block_216;
}
else
{
size_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_218 = lean_usize_of_nat(x_197);
x_219 = l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___redArg(x_136, x_144, x_218, x_4, x_147);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_unbox(x_220);
lean_dec(x_220);
x_198 = x_222;
x_199 = x_221;
goto block_216;
}
}
block_216:
{
if (x_198 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
lean_dec(x_148);
x_200 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_137, x_4, x_199);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = l_Lean_mkAppN(x_2, x_136);
x_204 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_203, x_4, x_202);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0;
x_208 = lean_nat_dec_lt(x_196, x_197);
if (x_208 == 0)
{
lean_dec(x_197);
lean_dec(x_136);
x_151 = x_205;
x_152 = x_201;
x_153 = x_207;
x_154 = x_206;
goto block_192;
}
else
{
uint8_t x_209; 
x_209 = lean_nat_dec_le(x_197, x_197);
if (x_209 == 0)
{
lean_dec(x_197);
lean_dec(x_136);
x_151 = x_205;
x_152 = x_201;
x_153 = x_207;
x_154 = x_206;
goto block_192;
}
else
{
size_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_usize_of_nat(x_197);
lean_dec(x_197);
x_211 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___redArg(x_136, x_144, x_210, x_207, x_4, x_206);
lean_dec(x_136);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_151 = x_205;
x_152 = x_201;
x_153 = x_212;
x_154 = x_213;
goto block_192;
}
}
}
else
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_197);
lean_dec(x_150);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_214 = lean_box(0);
if (lean_is_scalar(x_148)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_148;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_199);
return x_215;
}
}
}
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_150);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_223 = lean_ctor_get(x_149, 0);
lean_inc(x_223);
lean_dec(x_149);
if (lean_is_scalar(x_148)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_148;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_147);
return x_224;
}
block_192:
{
lean_object* x_155; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_155 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f(x_153, x_3, x_4, x_5, x_6, x_154);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_138);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_158 = x_155;
} else {
 lean_dec_ref(x_155);
 x_158 = lean_box(0);
}
x_159 = lean_box(0);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_157);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_166; lean_object* x_167; 
x_161 = lean_ctor_get(x_155, 1);
lean_inc(x_161);
lean_dec(x_155);
x_162 = lean_ctor_get(x_156, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_163 = x_156;
} else {
 lean_dec_ref(x_156);
 x_163 = lean_box(0);
}
x_164 = lean_box(0);
x_165 = lean_unbox(x_150);
x_166 = lean_unbox(x_164);
lean_inc(x_162);
x_167 = l_Lean_Meta_mkForallFVars(x_162, x_152, x_139, x_165, x_166, x_3, x_4, x_5, x_6, x_161);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_172; lean_object* x_173; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_box(1);
x_171 = lean_unbox(x_150);
lean_dec(x_150);
x_172 = lean_unbox(x_170);
x_173 = l_Lean_Meta_mkLambdaFVars(x_162, x_151, x_139, x_171, x_139, x_172, x_3, x_4, x_5, x_6, x_169);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_176 = x_173;
} else {
 lean_dec_ref(x_173);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_138;
}
lean_ctor_set(x_177, 0, x_168);
lean_ctor_set(x_177, 1, x_174);
if (lean_is_scalar(x_163)) {
 x_178 = lean_alloc_ctor(1, 1, 0);
} else {
 x_178 = x_163;
}
lean_ctor_set(x_178, 0, x_177);
if (lean_is_scalar(x_176)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_176;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_175);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_168);
lean_dec(x_163);
lean_dec(x_138);
x_180 = lean_ctor_get(x_173, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_173, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_182 = x_173;
} else {
 lean_dec_ref(x_173);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_138);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_184 = lean_ctor_get(x_167, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_167, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_186 = x_167;
} else {
 lean_dec_ref(x_167);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_138);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_188 = lean_ctor_get(x_155, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_155, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_190 = x_155;
} else {
 lean_dec_ref(x_155);
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
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_225 = lean_ctor_get(x_145, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_145, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_227 = x_145;
} else {
 lean_dec_ref(x_145);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_229 = lean_box(0);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_135);
return x_230;
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_231 = !lean_is_exclusive(x_8);
if (x_231 == 0)
{
return x_8;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_8, 0);
x_233 = lean_ctor_get(x_8, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_8);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_8, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Grind_eqResolution___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eqResolution___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = l_Lean_Meta_Grind_eqResolution___lam__0___closed__0;
x_17 = lean_array_push(x_16, x_2);
x_18 = lean_box(0);
x_19 = lean_box(1);
x_20 = lean_box(1);
x_21 = lean_unbox(x_18);
x_22 = lean_unbox(x_19);
x_23 = lean_unbox(x_18);
x_24 = lean_unbox(x_20);
x_25 = l_Lean_Meta_mkLambdaFVars(x_17, x_15, x_21, x_22, x_23, x_24, x_3, x_4, x_5, x_6, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_11, 1, x_27);
lean_ctor_set(x_25, 0, x_9);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_11, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_11);
lean_dec(x_14);
lean_free_object(x_9);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; 
x_35 = lean_ctor_get(x_11, 0);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_11);
x_37 = l_Lean_Meta_Grind_eqResolution___lam__0___closed__0;
x_38 = lean_array_push(x_37, x_2);
x_39 = lean_box(0);
x_40 = lean_box(1);
x_41 = lean_box(1);
x_42 = lean_unbox(x_39);
x_43 = lean_unbox(x_40);
x_44 = lean_unbox(x_39);
x_45 = lean_unbox(x_41);
x_46 = l_Lean_Meta_mkLambdaFVars(x_38, x_36, x_42, x_43, x_44, x_45, x_3, x_4, x_5, x_6, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_35);
lean_ctor_set(x_50, 1, x_47);
lean_ctor_set(x_9, 0, x_50);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_9);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_35);
lean_free_object(x_9);
x_52 = lean_ctor_get(x_46, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_54 = x_46;
} else {
 lean_dec_ref(x_46);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; 
x_56 = lean_ctor_get(x_9, 0);
lean_inc(x_56);
lean_dec(x_9);
x_57 = lean_ctor_get(x_8, 1);
lean_inc(x_57);
lean_dec(x_8);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_60 = x_56;
} else {
 lean_dec_ref(x_56);
 x_60 = lean_box(0);
}
x_61 = l_Lean_Meta_Grind_eqResolution___lam__0___closed__0;
x_62 = lean_array_push(x_61, x_2);
x_63 = lean_box(0);
x_64 = lean_box(1);
x_65 = lean_box(1);
x_66 = lean_unbox(x_63);
x_67 = lean_unbox(x_64);
x_68 = lean_unbox(x_63);
x_69 = lean_unbox(x_65);
x_70 = l_Lean_Meta_mkLambdaFVars(x_62, x_59, x_66, x_67, x_68, x_69, x_3, x_4, x_5, x_6, x_57);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_60;
}
lean_ctor_set(x_74, 0, x_58);
lean_ctor_set(x_74, 1, x_71);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_60);
lean_dec(x_58);
x_77 = lean_ctor_get(x_70, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_70, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_79 = x_70;
} else {
 lean_dec_ref(x_70);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_eqResolution___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_eqResolution___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_eqResolution___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eqResolution(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_eqResolution___lam__0), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Grind_eqResolution___closed__1;
x_9 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2___redArg(x_8, x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_EqResolution(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__0);
l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__1);
l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2);
l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___closed__0);
l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__0);
l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1);
l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__2);
l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__3);
l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__4);
l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0);
l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__1);
l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__0);
l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__1);
l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___closed__2);
l_Lean_Meta_Grind_eqResolution___lam__0___closed__0 = _init_l_Lean_Meta_Grind_eqResolution___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_eqResolution___lam__0___closed__0);
l_Lean_Meta_Grind_eqResolution___closed__0 = _init_l_Lean_Meta_Grind_eqResolution___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_eqResolution___closed__0);
l_Lean_Meta_Grind_eqResolution___closed__1 = _init_l_Lean_Meta_Grind_eqResolution___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_eqResolution___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
