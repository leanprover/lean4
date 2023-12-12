// Lean compiler output
// Module: Lean.Meta.Tactic.Replace
// Imports: Init Lean.Util.ForEachExpr Lean.Meta.AppBuilder Lean.Meta.MatchUtil Lean.Meta.Tactic.Util Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Clear Lean.Meta.Tactic.Assert
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
LEAN_EXPORT lean_object* l_Lean_Meta_changeLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_replaceTargetEq___lambda__1___closed__2;
static lean_object* l_Lean_MVarId_replaceTargetEq___closed__1;
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_change___lambda__2___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_replaceLocalDeclDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_modifyTarget___closed__2;
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__3;
lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_replaceLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_HashMap_insert___at_Lean_ForEachExpr_visit___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_change___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_change___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__1;
static lean_object* l_Lean_MVarId_changeLocalDecl___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_changeLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_MVarId_change___lambda__2___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_changeLocalDecl___lambda__1___closed__2;
lean_object* l_Lean_MVarId_assertAfter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_replaceTargetEq___lambda__1___closed__4;
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_ForEachExpr_visit___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_modifyTargetEqLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_changeLocalDecl___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_changeLocalDecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_change(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__2;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
static lean_object* l_Lean_MVarId_replaceTargetEq___closed__2;
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_change___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_replaceTargetEq___lambda__1___closed__1;
static lean_object* l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_changeLocalDecl___lambda__1___closed__4;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_change___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_change(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_change___lambda__2___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_changeLocalDecl___lambda__1___closed__1;
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_modifyTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_replaceTargetDefEq___closed__1;
static lean_object* l_Lean_MVarId_replaceTargetEq___lambda__1___closed__3;
static lean_object* l_Lean_MVarId_replaceTargetDefEq___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_changeLocalDecl___lambda__1___closed__5;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l_Lean_MVarId_modifyTarget___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_MVarId_changeLocalDecl___closed__3;
static lean_object* l_Lean_MVarId_change___lambda__2___closed__5;
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_MVarId_replaceTargetEq___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_replaceTargetEq___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mpr", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_replaceTargetEq___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_replaceTargetEq___lambda__1___closed__1;
x_2 = l_Lean_MVarId_replaceTargetEq___lambda__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_replaceTargetEq___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_1);
x_12 = l_Lean_MVarId_getTag(x_1, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_5);
lean_inc(x_3);
x_15 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_3, x_13, x_5, x_6, x_7, x_8, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_1);
x_18 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_21 = l_Lean_Meta_getLevel(x_19, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_19);
x_24 = l_Lean_Meta_mkEq(x_19, x_3, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l_Lean_Meta_mkExpectedTypeHint(x_4, x_25, x_5, x_6, x_7, x_8, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_MVarId_replaceTargetEq___lambda__1___closed__3;
x_33 = l_Lean_Expr_const___override(x_32, x_31);
x_34 = l_Lean_MVarId_replaceTargetEq___lambda__1___closed__4;
x_35 = lean_array_push(x_34, x_19);
x_36 = lean_array_push(x_35, x_3);
x_37 = lean_array_push(x_36, x_28);
lean_inc(x_16);
x_38 = lean_array_push(x_37, x_16);
x_39 = l_Lean_mkAppN(x_33, x_38);
x_40 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_39, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = l_Lean_Expr_mvarId_x21(x_16);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = l_Lean_Expr_mvarId_x21(x_16);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_27);
if (x_47 == 0)
{
return x_27;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_27, 0);
x_49 = lean_ctor_get(x_27, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_27);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_24);
if (x_51 == 0)
{
return x_24;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_24, 0);
x_53 = lean_ctor_get(x_24, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_24);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_21);
if (x_55 == 0)
{
return x_21;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_21, 0);
x_57 = lean_ctor_get(x_21, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_21);
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
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_18);
if (x_59 == 0)
{
return x_18;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_18, 0);
x_61 = lean_ctor_get(x_18, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_18);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_12);
if (x_63 == 0)
{
return x_12;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_12, 0);
x_65 = lean_ctor_get(x_12, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_12);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_10);
if (x_67 == 0)
{
return x_10;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_10, 0);
x_69 = lean_ctor_get(x_10, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_10);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_replaceTargetEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("replaceTarget", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_replaceTargetEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_replaceTargetEq___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_MVarId_replaceTargetEq___closed__2;
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_replaceTargetEq___lambda__1), 9, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_3);
x_11 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_replaceTargetEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_replaceTargetEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_1);
x_11 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_expr_eqv(x_13, x_3);
if (x_15 == 0)
{
lean_object* x_16; 
lean_free_object(x_11);
lean_inc(x_1);
x_16 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_4);
x_19 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_3, x_17, x_4, x_5, x_6, x_7, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_20);
x_22 = l_Lean_Meta_mkExpectedTypeHint(x_20, x_13, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_23, x_4, x_5, x_6, x_7, x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = l_Lean_Expr_mvarId_x21(x_20);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Lean_Expr_mvarId_x21(x_20);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_16);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_11, 0);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_11);
x_42 = lean_expr_eqv(x_40, x_3);
if (x_42 == 0)
{
lean_object* x_43; 
lean_inc(x_1);
x_43 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_4);
x_46 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_3, x_44, x_4, x_5, x_6, x_7, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_47);
x_49 = l_Lean_Meta_mkExpectedTypeHint(x_47, x_40, x_4, x_5, x_6, x_7, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_50, x_4, x_5, x_6, x_7, x_51);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = l_Lean_Expr_mvarId_x21(x_47);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_47);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_57 = lean_ctor_get(x_49, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_59 = x_49;
} else {
 lean_dec_ref(x_49);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_61 = lean_ctor_get(x_43, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_43, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_63 = x_43;
} else {
 lean_dec_ref(x_43);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; 
lean_dec(x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_41);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_11);
if (x_66 == 0)
{
return x_11;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_11, 0);
x_68 = lean_ctor_get(x_11, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_11);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_9);
if (x_70 == 0)
{
return x_9;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_9, 0);
x_72 = lean_ctor_get(x_9, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_9);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_replaceTargetDefEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("change", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_replaceTargetDefEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_replaceTargetDefEq___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_MVarId_replaceTargetDefEq___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_replaceTargetDefEq___lambda__1), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_replaceTargetDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_22; uint8_t x_23; 
x_22 = lean_st_ref_get(x_3, x_9);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_2);
x_26 = l_Lean_HashMapImp_find_x3f___at_Lean_ForEachExpr_visit___spec__1(x_24, x_2);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_free_object(x_22);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_27 = lean_apply_7(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_box(0);
x_10 = x_31;
x_11 = x_30;
goto block_21;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_35 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_10 = x_38;
x_11 = x_39;
goto block_21;
}
else
{
uint8_t x_40; 
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
return x_35;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_35, 0);
x_46 = lean_ctor_get(x_35, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_35);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
lean_dec(x_27);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 2);
lean_inc(x_50);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_51 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_48);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_10 = x_54;
x_11 = x_55;
goto block_21;
}
else
{
uint8_t x_56; 
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_53);
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
lean_dec(x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_51);
if (x_60 == 0)
{
return x_51;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_51, 0);
x_62 = lean_ctor_get(x_51, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_51);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
case 7:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_27, 1);
lean_inc(x_64);
lean_dec(x_27);
x_65 = lean_ctor_get(x_2, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_2, 2);
lean_inc(x_66);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_67 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_64);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_66, x_3, x_4, x_5, x_6, x_7, x_8, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_10 = x_70;
x_11 = x_71;
goto block_21;
}
else
{
uint8_t x_72; 
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_69);
if (x_72 == 0)
{
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 0);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_69);
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
lean_dec(x_66);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_67);
if (x_76 == 0)
{
return x_67;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_67, 0);
x_78 = lean_ctor_get(x_67, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_67);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
case 8:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_27, 1);
lean_inc(x_80);
lean_dec(x_27);
x_81 = lean_ctor_get(x_2, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_2, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_2, 3);
lean_inc(x_83);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_84 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_81, x_3, x_4, x_5, x_6, x_7, x_8, x_80);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_86 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_82, x_3, x_4, x_5, x_6, x_7, x_8, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_83, x_3, x_4, x_5, x_6, x_7, x_8, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_10 = x_89;
x_11 = x_90;
goto block_21;
}
else
{
uint8_t x_91; 
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_88);
if (x_91 == 0)
{
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_88, 0);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_88);
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
lean_dec(x_83);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_86);
if (x_95 == 0)
{
return x_86;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_86, 0);
x_97 = lean_ctor_get(x_86, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_86);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_84);
if (x_99 == 0)
{
return x_84;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_84, 0);
x_101 = lean_ctor_get(x_84, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_84);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
case 10:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_27, 1);
lean_inc(x_103);
lean_dec(x_27);
x_104 = lean_ctor_get(x_2, 1);
lean_inc(x_104);
x_105 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_104, x_3, x_4, x_5, x_6, x_7, x_8, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_10 = x_106;
x_11 = x_107;
goto block_21;
}
else
{
uint8_t x_108; 
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
return x_105;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_105, 0);
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_105);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
case 11:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_27, 1);
lean_inc(x_112);
lean_dec(x_27);
x_113 = lean_ctor_get(x_2, 2);
lean_inc(x_113);
x_114 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_113, x_3, x_4, x_5, x_6, x_7, x_8, x_112);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_10 = x_115;
x_11 = x_116;
goto block_21;
}
else
{
uint8_t x_117; 
lean_dec(x_2);
x_117 = !lean_is_exclusive(x_114);
if (x_117 == 0)
{
return x_114;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_114, 0);
x_119 = lean_ctor_get(x_114, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_114);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
default: 
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_121 = lean_ctor_get(x_27, 1);
lean_inc(x_121);
lean_dec(x_27);
x_122 = lean_box(0);
x_10 = x_122;
x_11 = x_121;
goto block_21;
}
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_27);
if (x_123 == 0)
{
return x_27;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_27, 0);
x_125 = lean_ctor_get(x_27, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_27);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_127 = lean_ctor_get(x_26, 0);
lean_inc(x_127);
lean_dec(x_26);
lean_ctor_set(x_22, 0, x_127);
return x_22;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_22, 0);
x_129 = lean_ctor_get(x_22, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_22);
lean_inc(x_2);
x_130 = l_Lean_HashMapImp_find_x3f___at_Lean_ForEachExpr_visit___spec__1(x_128, x_2);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_131 = lean_apply_7(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_box(0);
x_10 = x_135;
x_11 = x_134;
goto block_21;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_131, 1);
lean_inc(x_136);
lean_dec(x_131);
x_137 = lean_ctor_get(x_2, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_2, 1);
lean_inc(x_138);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_139 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_137, x_3, x_4, x_5, x_6, x_7, x_8, x_136);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_138, x_3, x_4, x_5, x_6, x_7, x_8, x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_10 = x_142;
x_11 = x_143;
goto block_21;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_2);
x_144 = lean_ctor_get(x_141, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_146 = x_141;
} else {
 lean_dec_ref(x_141);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_138);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_148 = lean_ctor_get(x_139, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_139, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_150 = x_139;
} else {
 lean_dec_ref(x_139);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
case 6:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_131, 1);
lean_inc(x_152);
lean_dec(x_131);
x_153 = lean_ctor_get(x_2, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_2, 2);
lean_inc(x_154);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_155 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_153, x_3, x_4, x_5, x_6, x_7, x_8, x_152);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_157 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_154, x_3, x_4, x_5, x_6, x_7, x_8, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_10 = x_158;
x_11 = x_159;
goto block_21;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_2);
x_160 = lean_ctor_get(x_157, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_162 = x_157;
} else {
 lean_dec_ref(x_157);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_154);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_164 = lean_ctor_get(x_155, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_155, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_166 = x_155;
} else {
 lean_dec_ref(x_155);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
case 7:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_131, 1);
lean_inc(x_168);
lean_dec(x_131);
x_169 = lean_ctor_get(x_2, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_2, 2);
lean_inc(x_170);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_171 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_169, x_3, x_4, x_5, x_6, x_7, x_8, x_168);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
x_173 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_170, x_3, x_4, x_5, x_6, x_7, x_8, x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_10 = x_174;
x_11 = x_175;
goto block_21;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_2);
x_176 = lean_ctor_get(x_173, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_173, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_178 = x_173;
} else {
 lean_dec_ref(x_173);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_170);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_180 = lean_ctor_get(x_171, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_171, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_182 = x_171;
} else {
 lean_dec_ref(x_171);
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
case 8:
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_184 = lean_ctor_get(x_131, 1);
lean_inc(x_184);
lean_dec(x_131);
x_185 = lean_ctor_get(x_2, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_2, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_2, 3);
lean_inc(x_187);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_188 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_185, x_3, x_4, x_5, x_6, x_7, x_8, x_184);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_190 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_186, x_3, x_4, x_5, x_6, x_7, x_8, x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec(x_190);
x_192 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_187, x_3, x_4, x_5, x_6, x_7, x_8, x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_10 = x_193;
x_11 = x_194;
goto block_21;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_2);
x_195 = lean_ctor_get(x_192, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_192, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_197 = x_192;
} else {
 lean_dec_ref(x_192);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_187);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_199 = lean_ctor_get(x_190, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_190, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_201 = x_190;
} else {
 lean_dec_ref(x_190);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_ctor_get(x_188, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_188, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_205 = x_188;
} else {
 lean_dec_ref(x_188);
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
case 10:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_131, 1);
lean_inc(x_207);
lean_dec(x_131);
x_208 = lean_ctor_get(x_2, 1);
lean_inc(x_208);
x_209 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_208, x_3, x_4, x_5, x_6, x_7, x_8, x_207);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_10 = x_210;
x_11 = x_211;
goto block_21;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_2);
x_212 = lean_ctor_get(x_209, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_209, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_214 = x_209;
} else {
 lean_dec_ref(x_209);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
}
case 11:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_131, 1);
lean_inc(x_216);
lean_dec(x_131);
x_217 = lean_ctor_get(x_2, 2);
lean_inc(x_217);
x_218 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_217, x_3, x_4, x_5, x_6, x_7, x_8, x_216);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_10 = x_219;
x_11 = x_220;
goto block_21;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_2);
x_221 = lean_ctor_get(x_218, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_218, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_223 = x_218;
} else {
 lean_dec_ref(x_218);
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
default: 
{
lean_object* x_225; lean_object* x_226; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_225 = lean_ctor_get(x_131, 1);
lean_inc(x_225);
lean_dec(x_131);
x_226 = lean_box(0);
x_10 = x_226;
x_11 = x_225;
goto block_21;
}
}
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_227 = lean_ctor_get(x_131, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_131, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_229 = x_131;
} else {
 lean_dec_ref(x_131);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_231 = lean_ctor_get(x_130, 0);
lean_inc(x_231);
lean_dec(x_130);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_129);
return x_232;
}
}
block_21:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_st_ref_take(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
x_15 = l_Lean_HashMap_insert___at_Lean_ForEachExpr_visit___spec__3(x_13, x_2, x_10);
x_16 = lean_st_ref_set(x_3, x_15, x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_10);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isFVar(x_1);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_9 = l_Lean_Expr_hasFVar(x_1);
lean_dec(x_1);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_fvarId_x21(x_1);
x_13 = l_Lean_FVarId_getDecl(x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_2, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_LocalDecl_index(x_17);
x_20 = l_Lean_LocalDecl_index(x_14);
x_21 = lean_nat_dec_lt(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_14);
x_22 = lean_st_ref_set(x_2, x_17, x_18);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_17);
x_31 = lean_st_ref_set(x_2, x_14, x_18);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = 0;
x_35 = lean_box(x_34);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
return x_13;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__1;
x_9 = lean_st_mk_ref(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__2;
x_13 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_12, x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_10, x_15);
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_10);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_FVarId_getDecl(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = l_Lean_Expr_fvar___override(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Meta_mkEqMP(x_2, x_13, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_3);
x_17 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_3, x_5, x_6, x_7, x_8, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_11);
x_20 = lean_st_mk_ref(x_11, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_21);
x_23 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar(x_18, x_21, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_get(x_21, x_24);
lean_dec(x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_LocalDecl_fvarId(x_26);
lean_dec(x_26);
x_29 = l_Lean_LocalDecl_userName(x_11);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_30 = l_Lean_MVarId_assertAfter(x_4, x_28, x_29, x_3, x_15, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 2);
lean_inc(x_35);
x_36 = l_Lean_Meta_saveState___rarg(x_6, x_7, x_8, x_32);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_39 = l_Lean_MVarId_clear(x_34, x_1, x_5, x_6, x_7, x_8, x_38);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_31, 2);
lean_dec(x_41);
x_42 = lean_ctor_get(x_31, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_31, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_39, 0);
lean_ctor_set(x_31, 1, x_45);
lean_ctor_set(x_39, 0, x_31);
return x_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
lean_ctor_set(x_31, 1, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_31);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_31);
x_49 = lean_ctor_get(x_39, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_51 = x_39;
} else {
 lean_dec_ref(x_39);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_33);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_35);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_35);
lean_dec(x_33);
x_54 = !lean_is_exclusive(x_39);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get(x_39, 1);
x_57 = l_Lean_Exception_isRuntime(x_55);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
lean_free_object(x_39);
lean_dec(x_55);
x_58 = l_Lean_Meta_SavedState_restore(x_37, x_5, x_6, x_7, x_8, x_56);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_37);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
lean_ctor_set(x_58, 0, x_31);
return x_58;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_31);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
uint8_t x_63; 
x_63 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
if (x_63 == 0)
{
lean_dec(x_37);
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_39;
}
else
{
lean_object* x_64; uint8_t x_65; 
lean_free_object(x_39);
lean_dec(x_55);
x_64 = l_Lean_Meta_SavedState_restore(x_37, x_5, x_6, x_7, x_8, x_56);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_37);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set(x_64, 0, x_31);
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_31);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_39, 0);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_39);
x_71 = l_Lean_Exception_isRuntime(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_69);
x_72 = l_Lean_Meta_SavedState_restore(x_37, x_5, x_6, x_7, x_8, x_70);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_37);
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
lean_ctor_set(x_75, 0, x_31);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
else
{
uint8_t x_76; 
x_76 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_37);
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_70);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_69);
x_78 = l_Lean_Meta_SavedState_restore(x_37, x_5, x_6, x_7, x_8, x_70);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_37);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_31);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_30);
if (x_82 == 0)
{
return x_30;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_30, 0);
x_84 = lean_ctor_get(x_30, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_30);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_23);
if (x_86 == 0)
{
return x_23;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_23, 0);
x_88 = lean_ctor_get(x_23, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_23);
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
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_14);
if (x_90 == 0)
{
return x_14;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_14, 0);
x_92 = lean_ctor_get(x_14, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_14);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_10);
if (x_94 == 0)
{
return x_10;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_10, 0);
x_96 = lean_ctor_get(x_10, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_10);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore___lambda__1), 9, 4);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_1);
x_11 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_replaceLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_FVarId_getType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_expr_eqv(x_2, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_free_object(x_9);
lean_inc(x_3);
x_14 = l_Lean_MVarId_getDecl(x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
x_18 = l_Lean_Meta_getLocalInstances(x_4, x_5, x_6, x_7, x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_17);
x_21 = lean_local_ctx_find(x_17, x_1);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_2);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_15, 2);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_15, sizeof(void*)*7);
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_Meta_mkFreshExprMVarAt(x_17, x_22, x_24, x_25, x_26, x_27, x_4, x_5, x_6, x_7, x_23);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_29);
x_31 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_3, x_29, x_4, x_5, x_6, x_7, x_30);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = l_Lean_Expr_mvarId_x21(x_29);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = l_Lean_Expr_mvarId_x21(x_29);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_17, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_17, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_21);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_42 = lean_ctor_get(x_21, 0);
x_43 = lean_ctor_get(x_18, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_dec(x_18);
x_45 = l_Lean_LocalDecl_setType(x_42, x_2);
x_46 = l_Lean_LocalDecl_fvarId(x_45);
lean_inc(x_45);
x_47 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_19, x_46, x_45);
x_48 = l_Lean_LocalDecl_index(x_45);
lean_ctor_set(x_21, 0, x_45);
x_49 = l_Lean_PersistentArray_set___rarg(x_20, x_48, x_21);
lean_dec(x_48);
lean_ctor_set(x_17, 1, x_49);
lean_ctor_set(x_17, 0, x_47);
x_50 = lean_ctor_get(x_15, 2);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_15, sizeof(void*)*7);
x_52 = lean_ctor_get(x_15, 0);
lean_inc(x_52);
lean_dec(x_15);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Lean_Meta_mkFreshExprMVarAt(x_17, x_43, x_50, x_51, x_52, x_53, x_4, x_5, x_6, x_7, x_44);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_55);
x_57 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_3, x_55, x_4, x_5, x_6, x_7, x_56);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
x_60 = l_Lean_Expr_mvarId_x21(x_55);
lean_ctor_set(x_57, 0, x_60);
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
x_62 = l_Lean_Expr_mvarId_x21(x_55);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_64 = lean_ctor_get(x_21, 0);
lean_inc(x_64);
lean_dec(x_21);
x_65 = lean_ctor_get(x_18, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_18, 1);
lean_inc(x_66);
lean_dec(x_18);
x_67 = l_Lean_LocalDecl_setType(x_64, x_2);
x_68 = l_Lean_LocalDecl_fvarId(x_67);
lean_inc(x_67);
x_69 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_19, x_68, x_67);
x_70 = l_Lean_LocalDecl_index(x_67);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_67);
x_72 = l_Lean_PersistentArray_set___rarg(x_20, x_70, x_71);
lean_dec(x_70);
lean_ctor_set(x_17, 1, x_72);
lean_ctor_set(x_17, 0, x_69);
x_73 = lean_ctor_get(x_15, 2);
lean_inc(x_73);
x_74 = lean_ctor_get_uint8(x_15, sizeof(void*)*7);
x_75 = lean_ctor_get(x_15, 0);
lean_inc(x_75);
lean_dec(x_15);
x_76 = lean_unsigned_to_nat(0u);
x_77 = l_Lean_Meta_mkFreshExprMVarAt(x_17, x_65, x_73, x_74, x_75, x_76, x_4, x_5, x_6, x_7, x_66);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_78);
x_80 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_3, x_78, x_4, x_5, x_6, x_7, x_79);
lean_dec(x_4);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
x_83 = l_Lean_Expr_mvarId_x21(x_78);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_17);
x_85 = lean_ctor_get(x_21, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_86 = x_21;
} else {
 lean_dec_ref(x_21);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_18, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_18, 1);
lean_inc(x_88);
lean_dec(x_18);
x_89 = l_Lean_LocalDecl_setType(x_85, x_2);
x_90 = l_Lean_LocalDecl_fvarId(x_89);
lean_inc(x_89);
x_91 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_19, x_90, x_89);
x_92 = l_Lean_LocalDecl_index(x_89);
if (lean_is_scalar(x_86)) {
 x_93 = lean_alloc_ctor(1, 1, 0);
} else {
 x_93 = x_86;
}
lean_ctor_set(x_93, 0, x_89);
x_94 = l_Lean_PersistentArray_set___rarg(x_20, x_92, x_93);
lean_dec(x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_ctor_get(x_15, 2);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_15, sizeof(void*)*7);
x_98 = lean_ctor_get(x_15, 0);
lean_inc(x_98);
lean_dec(x_15);
x_99 = lean_unsigned_to_nat(0u);
x_100 = l_Lean_Meta_mkFreshExprMVarAt(x_95, x_87, x_96, x_97, x_98, x_99, x_4, x_5, x_6, x_7, x_88);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_101);
x_103 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_3, x_101, x_4, x_5, x_6, x_7, x_102);
lean_dec(x_4);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = l_Lean_Expr_mvarId_x21(x_101);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_14);
if (x_108 == 0)
{
return x_14;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_14, 0);
x_110 = lean_ctor_get(x_14, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_14);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_9, 0);
x_113 = lean_ctor_get(x_9, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_9);
x_114 = lean_expr_eqv(x_2, x_112);
lean_dec(x_112);
if (x_114 == 0)
{
lean_object* x_115; 
lean_inc(x_3);
x_115 = l_Lean_MVarId_getDecl(x_3, x_4, x_5, x_6, x_7, x_113);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_ctor_get(x_4, 1);
lean_inc(x_118);
x_119 = l_Lean_Meta_getLocalInstances(x_4, x_5, x_6, x_7, x_117);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_inc(x_118);
x_122 = lean_local_ctx_find(x_118, x_1);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_2);
x_123 = lean_ctor_get(x_119, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_dec(x_119);
x_125 = lean_ctor_get(x_116, 2);
lean_inc(x_125);
x_126 = lean_ctor_get_uint8(x_116, sizeof(void*)*7);
x_127 = lean_ctor_get(x_116, 0);
lean_inc(x_127);
lean_dec(x_116);
x_128 = lean_unsigned_to_nat(0u);
x_129 = l_Lean_Meta_mkFreshExprMVarAt(x_118, x_123, x_125, x_126, x_127, x_128, x_4, x_5, x_6, x_7, x_124);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
lean_inc(x_130);
x_132 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_3, x_130, x_4, x_5, x_6, x_7, x_131);
lean_dec(x_4);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
x_135 = l_Lean_Expr_mvarId_x21(x_130);
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_133);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_137 = x_118;
} else {
 lean_dec_ref(x_118);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_122, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_139 = x_122;
} else {
 lean_dec_ref(x_122);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_119, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_119, 1);
lean_inc(x_141);
lean_dec(x_119);
x_142 = l_Lean_LocalDecl_setType(x_138, x_2);
x_143 = l_Lean_LocalDecl_fvarId(x_142);
lean_inc(x_142);
x_144 = l_Lean_PersistentHashMap_insert___at_Lean_LocalContext_mkLocalDecl___spec__1(x_120, x_143, x_142);
x_145 = l_Lean_LocalDecl_index(x_142);
if (lean_is_scalar(x_139)) {
 x_146 = lean_alloc_ctor(1, 1, 0);
} else {
 x_146 = x_139;
}
lean_ctor_set(x_146, 0, x_142);
x_147 = l_Lean_PersistentArray_set___rarg(x_121, x_145, x_146);
lean_dec(x_145);
if (lean_is_scalar(x_137)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_137;
}
lean_ctor_set(x_148, 0, x_144);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_ctor_get(x_116, 2);
lean_inc(x_149);
x_150 = lean_ctor_get_uint8(x_116, sizeof(void*)*7);
x_151 = lean_ctor_get(x_116, 0);
lean_inc(x_151);
lean_dec(x_116);
x_152 = lean_unsigned_to_nat(0u);
x_153 = l_Lean_Meta_mkFreshExprMVarAt(x_148, x_140, x_149, x_150, x_151, x_152, x_4, x_5, x_6, x_7, x_141);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
lean_inc(x_154);
x_156 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_3, x_154, x_4, x_5, x_6, x_7, x_155);
lean_dec(x_4);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
x_159 = l_Lean_Expr_mvarId_x21(x_154);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_157);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_ctor_get(x_115, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_115, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_163 = x_115;
} else {
 lean_dec_ref(x_115);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
lean_object* x_165; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_3);
lean_ctor_set(x_165, 1, x_113);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_9);
if (x_166 == 0)
{
return x_9;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_9, 0);
x_168 = lean_ctor_get(x_9, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_9);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_replaceLocalDeclDefEq___lambda__1___boxed), 8, 3);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_1);
x_10 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_replaceLocalDeclDefEq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_replaceLocalDeclDefEq___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_replaceLocalDeclDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_replaceLocalDeclDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_MVarId_change___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("given type", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_change___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_change___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_change___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nis not definitionally equal to", 31);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_change___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_change___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_change___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_change___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_change___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
if (x_3 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_2, x_4, x_5, x_6, x_7, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_12);
x_14 = l_Lean_Meta_isExprDefEq(x_12, x_2, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_indentExpr(x_2);
x_19 = l_Lean_MVarId_change___lambda__2___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_MVarId_change___lambda__2___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_indentExpr(x_12);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_MVarId_change___lambda__2___closed__6;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_MVarId_replaceTargetDefEq___closed__2;
x_28 = l_Lean_Meta_throwTacticEx___rarg(x_27, x_1, x_26, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_12);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_dec(x_14);
x_34 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_2, x_4, x_5, x_6, x_7, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_9);
if (x_39 == 0)
{
return x_9;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_9, 0);
x_41 = lean_ctor_get(x_9, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_9);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(x_3);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_change___lambda__2___boxed), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_9);
x_11 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_change___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_MVarId_change___lambda__2(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_change___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_MVarId_change(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_change(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(x_3);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_change___boxed), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_9);
x_11 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_change___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_change(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_MVarId_changeLocalDecl___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("changeHypothesis", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_changeLocalDecl___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_changeLocalDecl___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_changeLocalDecl___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected auxiliary target", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_changeLocalDecl___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_changeLocalDecl___lambda__1___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_changeLocalDecl___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_changeLocalDecl___lambda__1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
switch (lean_obj_tag(x_11)) {
case 7:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 2);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 8);
lean_dec(x_11);
if (x_4 == 0)
{
uint8_t x_68; 
x_68 = 0;
x_17 = x_68;
goto block_67;
}
else
{
uint8_t x_69; 
x_69 = 1;
x_17 = x_69;
goto block_67;
}
block_67:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_dec(x_14);
x_18 = x_12;
goto block_42;
}
else
{
lean_object* x_43; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
lean_inc(x_2);
x_43 = l_Lean_Meta_isExprDefEq(x_2, x_14, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_3);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l_Lean_indentExpr(x_2);
x_48 = l_Lean_MVarId_change___lambda__2___closed__2;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_MVarId_change___lambda__2___closed__4;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_indentExpr(x_14);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_MVarId_change___lambda__2___closed__6;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_MVarId_changeLocalDecl___lambda__1___closed__2;
x_57 = l_Lean_Meta_throwTacticEx___rarg(x_56, x_1, x_55, x_5, x_6, x_7, x_8, x_46);
lean_dec(x_8);
lean_dec(x_6);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
lean_object* x_62; 
lean_dec(x_14);
x_62 = lean_ctor_get(x_43, 1);
lean_inc(x_62);
lean_dec(x_43);
x_18 = x_62;
goto block_42;
}
}
else
{
uint8_t x_63; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_43);
if (x_63 == 0)
{
return x_43;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_43, 0);
x_65 = lean_ctor_get(x_43, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_43);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
block_42:
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_Expr_forallE___override(x_13, x_2, x_15, x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_19, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = 0;
x_25 = 1;
x_26 = l_Lean_Meta_introNCore(x_21, x_3, x_23, x_24, x_25, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
return x_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_20, 0);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_20);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
case 8:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_10, 1);
lean_inc(x_70);
lean_dec(x_10);
x_71 = lean_ctor_get(x_11, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_11, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_11, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_11, 3);
lean_inc(x_74);
lean_dec(x_11);
if (x_4 == 0)
{
uint8_t x_126; 
x_126 = 0;
x_75 = x_126;
goto block_125;
}
else
{
uint8_t x_127; 
x_127 = 1;
x_75 = x_127;
goto block_125;
}
block_125:
{
lean_object* x_76; 
if (x_75 == 0)
{
lean_dec(x_72);
x_76 = x_70;
goto block_100;
}
else
{
lean_object* x_101; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_72);
lean_inc(x_2);
x_101 = l_Lean_Meta_isExprDefEq(x_2, x_72, x_5, x_6, x_7, x_8, x_70);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_3);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_105 = l_Lean_indentExpr(x_2);
x_106 = l_Lean_MVarId_change___lambda__2___closed__2;
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = l_Lean_MVarId_change___lambda__2___closed__4;
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_indentExpr(x_72);
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_MVarId_change___lambda__2___closed__6;
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_MVarId_changeLocalDecl___lambda__1___closed__2;
x_115 = l_Lean_Meta_throwTacticEx___rarg(x_114, x_1, x_113, x_5, x_6, x_7, x_8, x_104);
lean_dec(x_8);
lean_dec(x_6);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
return x_115;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_115);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
else
{
lean_object* x_120; 
lean_dec(x_72);
x_120 = lean_ctor_get(x_101, 1);
lean_inc(x_120);
lean_dec(x_101);
x_76 = x_120;
goto block_100;
}
}
else
{
uint8_t x_121; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_101);
if (x_121 == 0)
{
return x_101;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_101, 0);
x_123 = lean_ctor_get(x_101, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_101);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
block_100:
{
uint8_t x_77; lean_object* x_78; lean_object* x_79; 
x_77 = 0;
x_78 = l_Lean_Expr_letE___override(x_71, x_2, x_73, x_74, x_77);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_79 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_78, x_5, x_6, x_7, x_8, x_76);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_box(0);
x_83 = 1;
x_84 = l_Lean_Meta_introNCore(x_80, x_3, x_82, x_77, x_83, x_5, x_6, x_7, x_8, x_81);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
lean_ctor_set(x_84, 0, x_87);
return x_84;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_84, 0);
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_84);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_84);
if (x_92 == 0)
{
return x_84;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_84, 0);
x_94 = lean_ctor_get(x_84, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_84);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_96 = !lean_is_exclusive(x_79);
if (x_96 == 0)
{
return x_79;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_79, 0);
x_98 = lean_ctor_get(x_79, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_79);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
}
default: 
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_128 = lean_ctor_get(x_10, 1);
lean_inc(x_128);
lean_dec(x_10);
x_129 = l_Lean_MVarId_changeLocalDecl___lambda__1___closed__2;
x_130 = l_Lean_MVarId_changeLocalDecl___lambda__1___closed__5;
x_131 = l_Lean_Meta_throwTacticEx___rarg(x_129, x_1, x_130, x_5, x_6, x_7, x_8, x_128);
lean_dec(x_8);
lean_dec(x_6);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_10);
if (x_132 == 0)
{
return x_10;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_10, 0);
x_134 = lean_ctor_get(x_10, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_10);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_changeLocalDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("changeLocalDecl", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_changeLocalDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_changeLocalDecl___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_changeLocalDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_MVarId_changeLocalDecl___closed__2;
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_1);
x_11 = l_Lean_MVarId_checkNotAssigned(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_MVarId_changeLocalDecl___closed__3;
x_14 = lean_array_push(x_13, x_2);
x_15 = 1;
x_16 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_MVarId_revert(x_1, x_14, x_15, x_16, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_array_get_size(x_20);
lean_dec(x_20);
x_23 = lean_box(x_4);
lean_inc(x_21);
x_24 = lean_alloc_closure((void*)(l_Lean_MVarId_changeLocalDecl___lambda__1___boxed), 9, 4);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_3);
lean_closure_set(x_24, 2, x_22);
lean_closure_set(x_24, 3, x_23);
x_25 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_21, x_24, x_5, x_6, x_7, x_8, x_19);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
return x_11;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_11, 0);
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_11);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_MVarId_changeLocalDecl___lambda__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_changeLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_MVarId_changeLocalDecl(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_changeLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_changeLocalDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_changeLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_changeLocalDecl(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_1);
x_11 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = lean_apply_6(x_3, x_12, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 0;
x_18 = l_Lean_MVarId_change(x_1, x_15, x_17, x_4, x_5, x_6, x_7, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_modifyTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("modifyTarget", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_modifyTarget___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_modifyTarget___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_MVarId_modifyTarget___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_modifyTarget___lambda__1), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_modifyTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_modifyTarget(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("modifyTargetEqLHS", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("equality expected", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Meta_matchEq_x3f(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_indentExpr(x_3);
x_13 = l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__4;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_MVarId_change___lambda__2___closed__6;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__2;
x_18 = l_Lean_Meta_throwTacticEx___rarg(x_17, x_1, x_16, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = lean_apply_6(x_2, x_22, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_mkEq(x_25, x_23, x_4, x_5, x_6, x_7, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
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
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_modifyTargetEqLHS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_modifyTargetEqLHS___lambda__1), 8, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_MVarId_modifyTarget(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_modifyTargetEqLHS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_modifyTargetEqLHS(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_MVarId_replaceTargetEq___lambda__1___closed__1 = _init_l_Lean_MVarId_replaceTargetEq___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_replaceTargetEq___lambda__1___closed__1);
l_Lean_MVarId_replaceTargetEq___lambda__1___closed__2 = _init_l_Lean_MVarId_replaceTargetEq___lambda__1___closed__2();
lean_mark_persistent(l_Lean_MVarId_replaceTargetEq___lambda__1___closed__2);
l_Lean_MVarId_replaceTargetEq___lambda__1___closed__3 = _init_l_Lean_MVarId_replaceTargetEq___lambda__1___closed__3();
lean_mark_persistent(l_Lean_MVarId_replaceTargetEq___lambda__1___closed__3);
l_Lean_MVarId_replaceTargetEq___lambda__1___closed__4 = _init_l_Lean_MVarId_replaceTargetEq___lambda__1___closed__4();
lean_mark_persistent(l_Lean_MVarId_replaceTargetEq___lambda__1___closed__4);
l_Lean_MVarId_replaceTargetEq___closed__1 = _init_l_Lean_MVarId_replaceTargetEq___closed__1();
lean_mark_persistent(l_Lean_MVarId_replaceTargetEq___closed__1);
l_Lean_MVarId_replaceTargetEq___closed__2 = _init_l_Lean_MVarId_replaceTargetEq___closed__2();
lean_mark_persistent(l_Lean_MVarId_replaceTargetEq___closed__2);
l_Lean_MVarId_replaceTargetDefEq___closed__1 = _init_l_Lean_MVarId_replaceTargetDefEq___closed__1();
lean_mark_persistent(l_Lean_MVarId_replaceTargetDefEq___closed__1);
l_Lean_MVarId_replaceTargetDefEq___closed__2 = _init_l_Lean_MVarId_replaceTargetDefEq___closed__2();
lean_mark_persistent(l_Lean_MVarId_replaceTargetDefEq___closed__2);
l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__1 = _init_l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__1);
l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__2 = _init_l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore_findMaxFVar___closed__2);
l_Lean_MVarId_change___lambda__2___closed__1 = _init_l_Lean_MVarId_change___lambda__2___closed__1();
lean_mark_persistent(l_Lean_MVarId_change___lambda__2___closed__1);
l_Lean_MVarId_change___lambda__2___closed__2 = _init_l_Lean_MVarId_change___lambda__2___closed__2();
lean_mark_persistent(l_Lean_MVarId_change___lambda__2___closed__2);
l_Lean_MVarId_change___lambda__2___closed__3 = _init_l_Lean_MVarId_change___lambda__2___closed__3();
lean_mark_persistent(l_Lean_MVarId_change___lambda__2___closed__3);
l_Lean_MVarId_change___lambda__2___closed__4 = _init_l_Lean_MVarId_change___lambda__2___closed__4();
lean_mark_persistent(l_Lean_MVarId_change___lambda__2___closed__4);
l_Lean_MVarId_change___lambda__2___closed__5 = _init_l_Lean_MVarId_change___lambda__2___closed__5();
lean_mark_persistent(l_Lean_MVarId_change___lambda__2___closed__5);
l_Lean_MVarId_change___lambda__2___closed__6 = _init_l_Lean_MVarId_change___lambda__2___closed__6();
lean_mark_persistent(l_Lean_MVarId_change___lambda__2___closed__6);
l_Lean_MVarId_changeLocalDecl___lambda__1___closed__1 = _init_l_Lean_MVarId_changeLocalDecl___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_changeLocalDecl___lambda__1___closed__1);
l_Lean_MVarId_changeLocalDecl___lambda__1___closed__2 = _init_l_Lean_MVarId_changeLocalDecl___lambda__1___closed__2();
lean_mark_persistent(l_Lean_MVarId_changeLocalDecl___lambda__1___closed__2);
l_Lean_MVarId_changeLocalDecl___lambda__1___closed__3 = _init_l_Lean_MVarId_changeLocalDecl___lambda__1___closed__3();
lean_mark_persistent(l_Lean_MVarId_changeLocalDecl___lambda__1___closed__3);
l_Lean_MVarId_changeLocalDecl___lambda__1___closed__4 = _init_l_Lean_MVarId_changeLocalDecl___lambda__1___closed__4();
lean_mark_persistent(l_Lean_MVarId_changeLocalDecl___lambda__1___closed__4);
l_Lean_MVarId_changeLocalDecl___lambda__1___closed__5 = _init_l_Lean_MVarId_changeLocalDecl___lambda__1___closed__5();
lean_mark_persistent(l_Lean_MVarId_changeLocalDecl___lambda__1___closed__5);
l_Lean_MVarId_changeLocalDecl___closed__1 = _init_l_Lean_MVarId_changeLocalDecl___closed__1();
lean_mark_persistent(l_Lean_MVarId_changeLocalDecl___closed__1);
l_Lean_MVarId_changeLocalDecl___closed__2 = _init_l_Lean_MVarId_changeLocalDecl___closed__2();
lean_mark_persistent(l_Lean_MVarId_changeLocalDecl___closed__2);
l_Lean_MVarId_changeLocalDecl___closed__3 = _init_l_Lean_MVarId_changeLocalDecl___closed__3();
lean_mark_persistent(l_Lean_MVarId_changeLocalDecl___closed__3);
l_Lean_MVarId_modifyTarget___closed__1 = _init_l_Lean_MVarId_modifyTarget___closed__1();
lean_mark_persistent(l_Lean_MVarId_modifyTarget___closed__1);
l_Lean_MVarId_modifyTarget___closed__2 = _init_l_Lean_MVarId_modifyTarget___closed__2();
lean_mark_persistent(l_Lean_MVarId_modifyTarget___closed__2);
l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__1 = _init_l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__1);
l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__2 = _init_l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__2();
lean_mark_persistent(l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__2);
l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__3 = _init_l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__3();
lean_mark_persistent(l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__3);
l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__4 = _init_l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__4();
lean_mark_persistent(l_Lean_MVarId_modifyTargetEqLHS___lambda__1___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
