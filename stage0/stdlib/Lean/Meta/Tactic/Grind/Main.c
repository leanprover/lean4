// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Main
// Imports: Init.Grind.Lemmas Lean.Meta.Tactic.Util Lean.Meta.Tactic.Grind.RevertAll Lean.Meta.Tactic.Grind.PropagatorAttr Lean.Meta.Tactic.Grind.Proj Lean.Meta.Tactic.Grind.ForallProp Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.Inv Lean.Meta.Tactic.Grind.Intro Lean.Meta.Tactic.Grind.EMatch
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__14;
lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_simp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_simple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Grind_ematchStar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessAndProbe___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__20;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__1;
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__11;
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedGoal___spec__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__2;
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_preprocessAndProbe___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessAndProbe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessAndProbe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__3;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Grind_main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MVarId_revertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_main___lambda__2___closed__2;
lean_object* l_Std_Queue_empty(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__1;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getFalseExpr___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__10;
lean_object* l_Lean_Meta_Grind_Goal_checkInvariants(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_main___lambda__2___closed__3;
static lean_object* l_Lean_Meta_Grind_main___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateProjEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getTrueExpr___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at_Lean_Meta_Grind_preprocessAndProbe___spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessAndProbe___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_preprocessAndProbe___closed__1;
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__15;
lean_object* l_ShareCommon_mkStateImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_builtinPropagatorsRef;
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__18;
static lean_object* l_Lean_Meta_Grind_main___lambda__2___closed__5;
lean_object* l_Lean_MVarId_clearAuxDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___rarg(lean_object*);
extern lean_object* l_Lean_Meta_Grind_grindNormSimprocExt;
static lean_object* l_Lean_Meta_Grind_main___closed__1;
lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_main___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__6;
lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_ensureNoMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_preprocessAndProbe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__1;
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__19;
static lean_object* l_Lean_Meta_Grind_main___lambda__2___closed__6;
uint64_t l_Lean_Name_hash___override(lean_object*);
extern lean_object* l_Lean_Meta_Grind_grindNormExt;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_transformTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_simp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__17;
lean_object* l_Lean_Meta_Grind_mkENodeCore(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at_Lean_Meta_Grind_preprocessAndProbe___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__4;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Grind_all___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_ensureProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__8;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__9;
lean_object* l_Lean_Meta_Grind_propagateForallProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_ShareCommon_objectFactory;
lean_object* lean_state_sharecommon(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkMethods___rarg___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_simple___closed__1;
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__16;
static lean_object* l_Lean_Meta_Grind_GrindM_run___rarg___closed__2;
lean_object* l_Lean_Meta_Grind_ppGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_betaReduce___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Meta_Grind_getEMatchTheorems___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Meta_Grind_propagateForallProp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Meta_Grind_propagateProjEq(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; size_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_Name_hash___override(x_17);
x_26 = 32;
x_27 = lean_uint64_shift_right(x_25, x_26);
x_28 = lean_uint64_xor(x_25, x_27);
x_29 = 16;
x_30 = lean_uint64_shift_right(x_28, x_29);
x_31 = lean_uint64_xor(x_28, x_30);
x_32 = lean_uint64_to_usize(x_31);
x_33 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_34 = 1;
x_35 = lean_usize_sub(x_33, x_34);
x_36 = lean_usize_land(x_32, x_35);
x_37 = lean_array_uget(x_23, x_36);
x_38 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1(x_17, x_37);
lean_dec(x_37);
lean_dec(x_17);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_box(0);
lean_ctor_set(x_18, 0, x_39);
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_free_object(x_18);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_apply_10(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_42 = lean_ctor_get(x_1, 0);
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_dec(x_18);
x_44 = lean_ctor_get(x_42, 1);
x_45 = lean_array_get_size(x_44);
x_46 = l_Lean_Name_hash___override(x_17);
x_47 = 32;
x_48 = lean_uint64_shift_right(x_46, x_47);
x_49 = lean_uint64_xor(x_46, x_48);
x_50 = 16;
x_51 = lean_uint64_shift_right(x_49, x_50);
x_52 = lean_uint64_xor(x_49, x_51);
x_53 = lean_uint64_to_usize(x_52);
x_54 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_55 = 1;
x_56 = lean_usize_sub(x_54, x_55);
x_57 = lean_usize_land(x_53, x_56);
x_58 = lean_array_uget(x_44, x_57);
x_59 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1(x_17, x_58);
lean_dec(x_58);
lean_dec(x_17);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_43);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_apply_10(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_68; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = lean_box(0);
lean_ctor_set(x_12, 0, x_68);
return x_12;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_12, 1);
lean_inc(x_69);
lean_dec(x_12);
x_70 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_70) == 4)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_72 = l_Lean_Meta_Grind_propagateProjEq(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_69);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; size_t x_85; size_t x_86; size_t x_87; size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; 
x_73 = lean_ctor_get(x_1, 0);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_73, 1);
x_77 = lean_array_get_size(x_76);
x_78 = l_Lean_Name_hash___override(x_71);
x_79 = 32;
x_80 = lean_uint64_shift_right(x_78, x_79);
x_81 = lean_uint64_xor(x_78, x_80);
x_82 = 16;
x_83 = lean_uint64_shift_right(x_81, x_82);
x_84 = lean_uint64_xor(x_81, x_83);
x_85 = lean_uint64_to_usize(x_84);
x_86 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_87 = 1;
x_88 = lean_usize_sub(x_86, x_87);
x_89 = lean_usize_land(x_85, x_88);
x_90 = lean_array_uget(x_76, x_89);
x_91 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1(x_71, x_90);
lean_dec(x_90);
lean_dec(x_71);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_box(0);
if (lean_is_scalar(x_75)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_75;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_74);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_75);
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_apply_10(x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_74);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_71);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_ctor_get(x_72, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_72, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_98 = x_72;
} else {
 lean_dec_ref(x_72);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_70);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_69);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_102 = !lean_is_exclusive(x_12);
if (x_102 == 0)
{
return x_12;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_12, 0);
x_104 = lean_ctor_get(x_12, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_12);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_array_get_size(x_16);
x_19 = l_Lean_Name_hash___override(x_14);
x_20 = 32;
x_21 = lean_uint64_shift_right(x_19, x_20);
x_22 = lean_uint64_xor(x_19, x_21);
x_23 = 16;
x_24 = lean_uint64_shift_right(x_22, x_23);
x_25 = lean_uint64_xor(x_22, x_24);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_28 = 1;
x_29 = lean_usize_sub(x_27, x_28);
x_30 = lean_usize_land(x_26, x_29);
x_31 = lean_array_uget(x_16, x_30);
lean_dec(x_16);
x_32 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1(x_14, x_31);
lean_dec(x_31);
lean_dec(x_14);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(0);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 0, x_33);
return x_13;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_free_object(x_13);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_apply_10(x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; size_t x_45; size_t x_46; size_t x_47; size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; 
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_dec(x_13);
x_37 = lean_array_get_size(x_36);
x_38 = l_Lean_Name_hash___override(x_14);
x_39 = 32;
x_40 = lean_uint64_shift_right(x_38, x_39);
x_41 = lean_uint64_xor(x_38, x_40);
x_42 = 16;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = lean_uint64_to_usize(x_44);
x_46 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_47 = 1;
x_48 = lean_usize_sub(x_46, x_47);
x_49 = lean_usize_land(x_45, x_48);
x_50 = lean_array_uget(x_36, x_49);
lean_dec(x_36);
x_51 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1(x_14, x_50);
lean_dec(x_50);
lean_dec(x_14);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_11);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_apply_10(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_11);
return x_57;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkMethods___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_builtinPropagatorsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Meta_Grind_mkMethods___rarg___closed__1;
x_3 = lean_st_ref_get(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___rarg___lambda__1___boxed), 11, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___rarg___lambda__2), 11, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___rarg___lambda__1___boxed), 11, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___rarg___lambda__2), 11, 1);
lean_closure_set(x_12, 0, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Grind_mkMethods___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_mkMethods___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_mkMethods(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ShareCommon_objectFactory;
x_2 = l_ShareCommon_mkStateImpl(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_ShareCommon_objectFactory;
x_2 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__1;
x_3 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__4;
x_4 = lean_state_sharecommon(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("True", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_grindNormExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_grindNormSimprocExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 2, 19);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 4, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 5, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 6, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 7, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 8, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 9, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 12, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 13, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 14, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 15, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 16, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 17, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 18, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__12;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__13;
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__13;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__16;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__18() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__17;
x_3 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__16;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__13;
x_2 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__18;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__15;
x_2 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__19;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_9 = lean_box(0);
x_10 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__5;
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = l_Lean_ShareCommon_objectFactory;
x_14 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__8;
x_15 = lean_state_sharecommon(x_13, x_12, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__9;
x_19 = l_Lean_Meta_SimpExtension_getTheorems(x_18, x_6, x_7, x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__10;
x_23 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_22, x_6, x_7, x_21);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_23, 1);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_9);
x_26 = lean_array_mk(x_23);
x_27 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_7, x_25);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_9);
lean_ctor_set(x_27, 0, x_20);
x_31 = lean_array_mk(x_27);
x_32 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__11;
x_33 = l_Lean_Meta_Simp_mkContext(x_32, x_31, x_29, x_4, x_5, x_6, x_7, x_30);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Meta_Grind_mkMethods___rarg(x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_26);
lean_ctor_set(x_39, 2, x_2);
lean_ctor_set(x_39, 3, x_3);
x_40 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__14;
x_41 = lean_unsigned_to_nat(1u);
x_42 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__13;
x_43 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__20;
x_44 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_17);
lean_ctor_set(x_44, 2, x_41);
lean_ctor_set(x_44, 3, x_42);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_44, 5, x_16);
lean_ctor_set(x_44, 6, x_11);
x_45 = lean_st_mk_ref(x_44, x_38);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_46);
x_48 = lean_apply_8(x_1, x_37, x_39, x_46, x_4, x_5, x_6, x_7, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_st_ref_get(x_46, x_50);
lean_dec(x_46);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set(x_51, 0, x_49);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_46);
x_56 = !lean_is_exclusive(x_48);
if (x_56 == 0)
{
return x_48;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_48);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_60 = lean_ctor_get(x_27, 0);
x_61 = lean_ctor_get(x_27, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_27);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_20);
lean_ctor_set(x_62, 1, x_9);
x_63 = lean_array_mk(x_62);
x_64 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__11;
x_65 = l_Lean_Meta_Simp_mkContext(x_64, x_63, x_60, x_4, x_5, x_6, x_7, x_61);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Meta_Grind_mkMethods___rarg(x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_26);
lean_ctor_set(x_71, 2, x_2);
lean_ctor_set(x_71, 3, x_3);
x_72 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__14;
x_73 = lean_unsigned_to_nat(1u);
x_74 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__13;
x_75 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__20;
x_76 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_17);
lean_ctor_set(x_76, 2, x_73);
lean_ctor_set(x_76, 3, x_74);
lean_ctor_set(x_76, 4, x_75);
lean_ctor_set(x_76, 5, x_16);
lean_ctor_set(x_76, 6, x_11);
x_77 = lean_st_mk_ref(x_76, x_70);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_78);
x_80 = lean_apply_8(x_1, x_69, x_71, x_78, x_4, x_5, x_6, x_7, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_st_ref_get(x_78, x_82);
lean_dec(x_78);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_78);
x_87 = lean_ctor_get(x_80, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_80, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_89 = x_80;
} else {
 lean_dec_ref(x_80);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_91 = lean_ctor_get(x_23, 0);
x_92 = lean_ctor_get(x_23, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_23);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_9);
x_94 = lean_array_mk(x_93);
x_95 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_7, x_92);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
 lean_ctor_set_tag(x_99, 1);
}
lean_ctor_set(x_99, 0, x_20);
lean_ctor_set(x_99, 1, x_9);
x_100 = lean_array_mk(x_99);
x_101 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__11;
x_102 = l_Lean_Meta_Simp_mkContext(x_101, x_100, x_96, x_4, x_5, x_6, x_7, x_97);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Lean_Meta_Grind_mkMethods___rarg(x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_94);
lean_ctor_set(x_108, 2, x_2);
lean_ctor_set(x_108, 3, x_3);
x_109 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__14;
x_110 = lean_unsigned_to_nat(1u);
x_111 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__13;
x_112 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__20;
x_113 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_113, 0, x_109);
lean_ctor_set(x_113, 1, x_17);
lean_ctor_set(x_113, 2, x_110);
lean_ctor_set(x_113, 3, x_111);
lean_ctor_set(x_113, 4, x_112);
lean_ctor_set(x_113, 5, x_16);
lean_ctor_set(x_113, 6, x_11);
x_114 = lean_st_mk_ref(x_113, x_107);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
lean_inc(x_115);
x_117 = lean_apply_8(x_1, x_106, x_108, x_115, x_4, x_5, x_6, x_7, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_st_ref_get(x_115, x_119);
lean_dec(x_115);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_118);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_115);
x_124 = lean_ctor_get(x_117, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_117, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_126 = x_117;
} else {
 lean_dec_ref(x_117);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_GrindM_run___rarg), 8, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__13;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_mk_ref(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = 1;
x_13 = 0;
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_12, x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Meta_Grind_mkENodeCore(x_2, x_12, x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_3, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_st_ref_get(x_3, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_19, 1, x_24);
lean_ctor_set(x_22, 0, x_19);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_22);
lean_ctor_set(x_19, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_st_ref_get(x_3, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_31);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
lean_ctor_set(x_1, 1, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Queue_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__3___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_10 = l_Lean_Meta_Grind_getTrueExpr___rarg(x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Grind_getFalseExpr___rarg(x_4, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_Grind_getEMatchTheorems___rarg(x_8, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__13;
x_20 = l_Lean_PersistentHashMap_empty___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__1;
x_21 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__1;
x_22 = 0;
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Meta_Grind_GrindM_run___rarg___closed__18;
x_25 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedGoal___spec__2;
x_26 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2;
lean_inc(x_1);
x_27 = lean_alloc_ctor(0, 14, 1);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_19);
lean_ctor_set(x_27, 3, x_20);
lean_ctor_set(x_27, 4, x_19);
lean_ctor_set(x_27, 5, x_21);
lean_ctor_set(x_27, 6, x_23);
lean_ctor_set(x_27, 7, x_23);
lean_ctor_set(x_27, 8, x_24);
lean_ctor_set(x_27, 9, x_24);
lean_ctor_set(x_27, 10, x_17);
lean_ctor_set(x_27, 11, x_23);
lean_ctor_set(x_27, 12, x_25);
lean_ctor_set(x_27, 13, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*14, x_22);
x_28 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__1___boxed), 9, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__2___boxed), 11, 2);
lean_closure_set(x_29, 0, x_14);
lean_closure_set(x_29, 1, x_11);
x_30 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_30, 0, x_28);
lean_closure_set(x_30, 1, x_29);
x_31 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__3;
x_32 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_32, 0, x_30);
lean_closure_set(x_32, 1, x_31);
x_33 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_1, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_33;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Meta_Grind_Goal_checkInvariants(x_12, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_1 = x_13;
x_9 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*14);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_2);
x_1 = x_10;
x_2 = x_11;
goto _start;
}
}
else
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_1 = x_13;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_unfoldReducible), 6, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MVarId_betaReduce___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_MVarId_ensureProp(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_1);
x_12 = l_Lean_MVarId_ensureNoMVar(x_1, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_MVarId_clearAuxDecls(x_1, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_MVarId_revertAll(x_15, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Lean_MVarId_transformTarget(x_18, x_20, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = l_Lean_MVarId_transformTarget(x_22, x_24, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_28 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_32 = l_Lean_Meta_Grind_intros(x_29, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_33);
x_35 = l_List_forM___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___spec__1(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
x_39 = l_List_filterTR_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___spec__2(x_33, x_38);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_box(0);
x_42 = l_List_filterTR_loop___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___spec__2(x_33, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_33);
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
else
{
uint8_t x_48; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_32);
if (x_48 == 0)
{
return x_32;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_32, 0);
x_50 = lean_ctor_get(x_32, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_32);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_28);
if (x_52 == 0)
{
return x_28;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_28, 0);
x_54 = lean_ctor_get(x_28, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_28);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_25);
if (x_56 == 0)
{
return x_25;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_25, 0);
x_58 = lean_ctor_get(x_25, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_25);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_21);
if (x_60 == 0)
{
return x_21;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_21, 0);
x_62 = lean_ctor_get(x_21, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_21);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_17);
if (x_64 == 0)
{
return x_17;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_17, 0);
x_66 = lean_ctor_get(x_17, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_17);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_14);
if (x_68 == 0)
{
return x_14;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_14, 0);
x_70 = lean_ctor_get(x_14, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_14);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_12);
if (x_72 == 0)
{
return x_12;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_12, 0);
x_74 = lean_ctor_get(x_12, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_12);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_10);
if (x_76 == 0)
{
return x_10;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_10, 0);
x_78 = lean_ctor_get(x_10, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_10);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Grind_all___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = lean_apply_9(x_1, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_List_appendTR___rarg(x_2, x_16);
x_2 = x_18;
x_3 = x_14;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_all(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_List_foldlM___at_Lean_Meta_Grind_all___spec__1(x_2, x_11, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_simple___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_ematchStar), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_simple(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_simple___closed__1;
x_11 = l_Lean_Meta_Grind_all(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Grind_main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(0);
x_12 = l_List_mapTR_loop___at_Lean_Meta_Grind_main___spec__1(x_1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("final", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_main___lambda__2___closed__1;
x_2 = l_Lean_Meta_Grind_main___lambda__2___closed__2;
x_3 = l_Lean_Meta_Grind_main___lambda__2___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_main___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_simple___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Meta_Grind_all(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Grind_main___lambda__2___closed__4;
x_15 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_simp___spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = l_Lean_Meta_Grind_main___lambda__1(x_12, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 1);
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_12);
x_24 = l_Lean_Meta_Grind_ppGoals(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_MessageData_ofFormat(x_25);
x_28 = l_Lean_Meta_Grind_main___lambda__2___closed__6;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_27);
lean_ctor_set(x_15, 0, x_28);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_addTrace___at_Lean_Meta_Grind_simp___spec__3(x_14, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Meta_Grind_main___lambda__1(x_12, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_31);
return x_33;
}
else
{
uint8_t x_34; 
lean_free_object(x_15);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_12);
x_39 = l_Lean_Meta_Grind_ppGoals(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_MessageData_ofFormat(x_40);
x_43 = l_Lean_Meta_Grind_main___lambda__2___closed__6;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_addTrace___at_Lean_Meta_Grind_simp___spec__3(x_14, x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Meta_Grind_main___lambda__1(x_12, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_47);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_ctor_get(x_39, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_52 = x_39;
} else {
 lean_dec_ref(x_39);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_11);
if (x_54 == 0)
{
return x_11;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_11, 0);
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_11);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_main___lambda__2), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore), 9, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Meta_Grind_main___closed__1;
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_Grind_GrindM_run___rarg(x_11, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_main___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_preprocessAndProbe___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_2);
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_2, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_st_ref_get(x_2, x_15);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_13, 1, x_18);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_13, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_st_ref_get(x_2, x_23);
lean_dec(x_2);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_25);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_Grind_preprocessAndProbe___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lambda__1___boxed), 9, 1);
lean_closure_set(x_16, 0, x_13);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_List_forM___at_Lean_Meta_Grind_preprocessAndProbe___spec__1___lambda__1), 10, 1);
lean_closure_set(x_17, 0, x_1);
x_18 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__3;
x_20 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_21 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__2___rarg(x_15, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_2 = x_14;
x_10 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at_Lean_Meta_Grind_preprocessAndProbe___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_st_ref_get(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_resetCache___rarg(x_3, x_4, x_5, x_13);
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_take(x_3, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
lean_ctor_set(x_17, 0, x_10);
x_21 = lean_st_ref_set(x_3, x_17, x_18);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_12);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_17, 1);
x_27 = lean_ctor_get(x_17, 2);
x_28 = lean_ctor_get(x_17, 3);
x_29 = lean_ctor_get(x_17, 4);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set(x_30, 4, x_29);
x_31 = lean_st_ref_set(x_3, x_30, x_18);
lean_dec(x_3);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_35 = lean_ctor_get(x_11, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_dec(x_11);
x_37 = l_Lean_Meta_resetCache___rarg(x_3, x_4, x_5, x_36);
lean_dec(x_5);
lean_dec(x_4);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_st_ref_take(x_3, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
lean_ctor_set(x_40, 0, x_10);
x_44 = lean_st_ref_set(x_3, x_40, x_41);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 0, x_35);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_35);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_40, 1);
x_50 = lean_ctor_get(x_40, 2);
x_51 = lean_ctor_get(x_40, 3);
x_52 = lean_ctor_get(x_40, 4);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_40);
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_10);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_53, 2, x_50);
lean_ctor_set(x_53, 3, x_51);
lean_ctor_set(x_53, 4, x_52);
x_54 = lean_st_ref_set(x_3, x_53, x_41);
lean_dec(x_3);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
 lean_ctor_set_tag(x_57, 1);
}
lean_ctor_set(x_57, 0, x_35);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at_Lean_Meta_Grind_preprocessAndProbe___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withoutModifyingMCtx___at_Lean_Meta_Grind_preprocessAndProbe___spec__2___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessAndProbe___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forM___at_Lean_Meta_Grind_preprocessAndProbe___spec__1(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessAndProbe___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_Meta_Grind_main___lambda__2___closed__4;
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_simp___spec__2(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = l_Lean_Meta_Grind_preprocessAndProbe___lambda__1(x_1, x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 1);
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Lean_Meta_Grind_ppGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_MessageData_ofFormat(x_22);
x_25 = l_Lean_Meta_Grind_main___lambda__2___closed__6;
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_24);
lean_ctor_set(x_12, 0, x_25);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_addTrace___at_Lean_Meta_Grind_simp___spec__3(x_11, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_Grind_preprocessAndProbe___lambda__1(x_1, x_2, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_28);
return x_30;
}
else
{
uint8_t x_31; 
lean_free_object(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_36 = l_Lean_Meta_Grind_ppGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_MessageData_ofFormat(x_37);
x_40 = l_Lean_Meta_Grind_main___lambda__2___closed__6;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_addTrace___at_Lean_Meta_Grind_simp___spec__3(x_11, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Meta_Grind_preprocessAndProbe___lambda__1(x_1, x_2, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_45);
lean_dec(x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_49 = x_36;
} else {
 lean_dec_ref(x_36);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocessAndProbe___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = lean_unsigned_to_nat(100u);
x_3 = lean_unsigned_to_nat(5u);
x_4 = lean_unsigned_to_nat(1000u);
x_5 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessAndProbe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore), 9, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_preprocessAndProbe___lambda__2), 10, 1);
lean_closure_set(x_10, 0, x_3);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg), 10, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_Grind_preprocessAndProbe___closed__1;
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_GrindM_run___rarg), 8, 3);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_12);
x_14 = l_Lean_Meta_withoutModifyingMCtx___at_Lean_Meta_Grind_preprocessAndProbe___spec__2___rarg(x_13, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessAndProbe___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_preprocessAndProbe___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Proj(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatch(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Proj(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Inv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EMatch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_mkMethods___rarg___closed__1 = _init_l_Lean_Meta_Grind_mkMethods___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_mkMethods___rarg___closed__1);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__1 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__1);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__2 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__2);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__3 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__3);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__4 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__4);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__5 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__5);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__6 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__6);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__7 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__7);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__8 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__8);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__9 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__9);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__10 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__10);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__11 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__11);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__12 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__12);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__13 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__13);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__14 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__14();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__14);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__15 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__15();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__15);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__16 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__16();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__16);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__17 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__17();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__17);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__18 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__18();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__18);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__19 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__19();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__19);
l_Lean_Meta_Grind_GrindM_run___rarg___closed__20 = _init_l_Lean_Meta_Grind_GrindM_run___rarg___closed__20();
lean_mark_persistent(l_Lean_Meta_Grind_GrindM_run___rarg___closed__20);
l_Lean_PersistentHashMap_empty___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__1 = _init_l_Lean_PersistentHashMap_empty___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__1();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___spec__1);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__1);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__2);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___closed__3);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__1);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___closed__2);
l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_simple___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_simple___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_simple___closed__1);
l_Lean_Meta_Grind_main___lambda__2___closed__1 = _init_l_Lean_Meta_Grind_main___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_main___lambda__2___closed__1);
l_Lean_Meta_Grind_main___lambda__2___closed__2 = _init_l_Lean_Meta_Grind_main___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_main___lambda__2___closed__2);
l_Lean_Meta_Grind_main___lambda__2___closed__3 = _init_l_Lean_Meta_Grind_main___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_main___lambda__2___closed__3);
l_Lean_Meta_Grind_main___lambda__2___closed__4 = _init_l_Lean_Meta_Grind_main___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_main___lambda__2___closed__4);
l_Lean_Meta_Grind_main___lambda__2___closed__5 = _init_l_Lean_Meta_Grind_main___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_main___lambda__2___closed__5);
l_Lean_Meta_Grind_main___lambda__2___closed__6 = _init_l_Lean_Meta_Grind_main___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_main___lambda__2___closed__6);
l_Lean_Meta_Grind_main___closed__1 = _init_l_Lean_Meta_Grind_main___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_main___closed__1);
l_Lean_Meta_Grind_preprocessAndProbe___closed__1 = _init_l_Lean_Meta_Grind_preprocessAndProbe___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_preprocessAndProbe___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
