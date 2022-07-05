// Lean compiler output
// Module: Lean.Meta.Match.CaseValues
// Imports: Init Lean.Meta.Tactic.Subst Lean.Meta.Tactic.Clear Lean.Meta.Match.Value
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
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues_loop(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_CaseValuesSubgoal_newHs___default___closed__1;
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__4;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_appendTagSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__8;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedCaseValueSubgoal___closed__1;
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_caseValues_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CaseValuesSubgoal_newHs___default;
lean_object* l_Lean_Meta_FVarSubst_domain(lean_object*);
static lean_object* l_Lean_Meta_caseValue___closed__4;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__10;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l_Lean_Meta_caseValue___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedCaseValueSubgoal;
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_CaseValuesSubgoal_subst___default;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__6;
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__1;
static lean_object* l_Lean_Meta_caseValues_loop___closed__4;
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValues_loop___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__11;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValue___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedCaseValuesSubgoal;
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CaseValueSubgoal_subst___default;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValue___closed__6;
static lean_object* l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__1;
static lean_object* l_Lean_Meta_caseValues_loop___closed__3;
lean_object* l_List_mapTRAux___at_Lean_Meta_substCore___spec__6(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValues_loop___closed__5;
static lean_object* l_Lean_Meta_caseValue___closed__5;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__7;
lean_object* l_Lean_mkFVar(lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2___closed__2;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_foldPatValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1___closed__1;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__2;
static lean_object* l_Lean_Meta_caseValues_loop___closed__2;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1___closed__2;
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValues_loop___closed__6;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_assignExprMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__3;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2___closed__1;
static lean_object* l_Lean_Meta_caseValues_loop___closed__1;
static lean_object* l_Lean_Meta_caseValue___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__4;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValues_loop___closed__7;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__3;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_caseValues_loop___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_CaseValueSubgoal_subst___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCaseValueSubgoal___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCaseValueSubgoal() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedCaseValueSubgoal___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_5;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
x_1 = x_8;
x_2 = x_9;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("found decl", 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = l_Lean_Meta_getLocalDecl(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_7, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
lean_inc(x_2);
x_22 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_2, x_4, x_5, x_6, x_7, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_4);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1___closed__2;
x_33 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_2, x_32, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_4);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_4);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_9);
if (x_34 == 0)
{
return x_9;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_9, 0);
x_36 = lean_ctor_get(x_9, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_9);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("searching for decl", 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_4);
x_10 = l_Lean_Meta_FVarSubst_get(x_1, x_2);
lean_dec(x_1);
x_11 = l_Lean_Expr_fvarId_x21(x_10);
x_22 = lean_st_ref_get(x_8, x_9);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 3);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get_uint8(x_24, sizeof(void*)*1);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = 0;
x_12 = x_27;
x_13 = x_26;
goto block_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
lean_inc(x_3);
x_29 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_3, x_5, x_6, x_7, x_8, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unbox(x_30);
lean_dec(x_30);
x_12 = x_32;
x_13 = x_31;
goto block_21;
}
block_21:
{
if (x_12 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1(x_11, x_3, x_14, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2___closed__2;
lean_inc(x_3);
x_17 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_16, x_5, x_6, x_7, x_8, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1(x_11, x_3, x_18, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_18);
return x_20;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("subst domain: ", 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_st_ref_get(x_8, x_9);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 3);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get_uint8(x_29, sizeof(void*)*1);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = 0;
x_10 = x_32;
x_11 = x_31;
goto block_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
lean_inc(x_3);
x_34 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_3, x_5, x_6, x_7, x_8, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_unbox(x_35);
lean_dec(x_35);
x_10 = x_37;
x_11 = x_36;
goto block_26;
}
block_26:
{
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_1);
x_14 = l_Lean_Meta_FVarSubst_domain(x_1);
lean_inc(x_4);
x_15 = l_List_mapTRAux___at___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___spec__1(x_14, x_4);
x_16 = l_List_mapTRAux___at_Lean_Meta_substCore___spec__6(x_15, x_4);
x_17 = l_Lean_MessageData_ofList(x_16);
lean_dec(x_16);
x_18 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_inc(x_3);
x_22 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_21, x_5, x_6, x_7, x_8, x_11);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2(x_1, x_2, x_3, x_23, x_5, x_6, x_7, x_8, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("caseValue", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Not", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("dite", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__8;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_Meta_getMVarTag(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__2;
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_15 = l_Lean_Meta_checkNotAssigned(x_1, x_14, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_1);
x_17 = l_Lean_Meta_getMVarType(x_1, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_mkFVar(x_2);
x_21 = l_Lean_Meta_foldPatValue(x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Meta_mkEq(x_20, x_21, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__5;
lean_inc(x_23);
x_27 = l_Lean_mkApp(x_26, x_23);
x_28 = 0;
lean_inc(x_18);
lean_inc(x_23);
lean_inc(x_4);
x_29 = l_Lean_mkForall(x_4, x_28, x_23, x_18);
x_30 = l_Lean_mkForall(x_4, x_28, x_27, x_18);
lean_inc(x_6);
lean_inc(x_12);
x_31 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_29, x_12, x_6, x_7, x_8, x_9, x_24);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_6);
x_34 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_30, x_12, x_6, x_7, x_8, x_9, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_23);
lean_inc(x_32);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_32);
lean_inc(x_35);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_41 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__9;
x_42 = lean_array_push(x_41, x_38);
x_43 = lean_array_push(x_42, x_37);
x_44 = lean_array_push(x_43, x_39);
x_45 = lean_array_push(x_44, x_40);
x_46 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__7;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = l_Lean_Meta_mkAppOptM(x_46, x_45, x_6, x_7, x_8, x_9, x_36);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_st_ref_get(x_9, x_49);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_st_ref_take(x_7, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_53, 0);
x_57 = l_Lean_assignExprMVar(x_1, x_48, x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
lean_ctor_set(x_53, 0, x_58);
x_59 = lean_st_ref_set(x_7, x_53, x_54);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_Expr_mvarId_x21(x_35);
lean_dec(x_35);
x_62 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_63 = l_Lean_Meta_intro1Core(x_61, x_62, x_6, x_7, x_8, x_9, x_60);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
lean_inc(x_5);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set(x_68, 2, x_5);
x_69 = l_Lean_Expr_mvarId_x21(x_32);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_70 = l_Lean_Meta_intro1Core(x_69, x_62, x_6, x_7, x_8, x_9, x_65);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_73);
x_76 = l_Lean_Meta_substCore(x_74, x_73, x_75, x_5, x_75, x_75, x_6, x_7, x_8, x_9, x_72);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = !lean_is_exclusive(x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_77, 0);
x_81 = lean_ctor_get(x_77, 1);
x_82 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__11;
lean_inc(x_73);
lean_inc(x_80);
x_83 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3), 9, 4);
lean_closure_set(x_83, 0, x_80);
lean_closure_set(x_83, 1, x_73);
lean_closure_set(x_83, 2, x_82);
lean_closure_set(x_83, 3, x_25);
lean_inc(x_81);
x_84 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_81, x_83, x_6, x_7, x_8, x_9, x_78);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
x_87 = l_Lean_Meta_FVarSubst_get(x_80, x_73);
x_88 = l_Lean_Expr_fvarId_x21(x_87);
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_81);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 2, x_80);
lean_ctor_set(x_77, 1, x_68);
lean_ctor_set(x_77, 0, x_89);
lean_ctor_set(x_84, 0, x_77);
return x_84;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
lean_dec(x_84);
x_91 = l_Lean_Meta_FVarSubst_get(x_80, x_73);
x_92 = l_Lean_Expr_fvarId_x21(x_91);
x_93 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_93, 0, x_81);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_80);
lean_ctor_set(x_77, 1, x_68);
lean_ctor_set(x_77, 0, x_93);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_77);
lean_ctor_set(x_94, 1, x_90);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_free_object(x_77);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_73);
lean_dec(x_68);
x_95 = !lean_is_exclusive(x_84);
if (x_95 == 0)
{
return x_84;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_84, 0);
x_97 = lean_ctor_get(x_84, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_84);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_77, 0);
x_100 = lean_ctor_get(x_77, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_77);
x_101 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__11;
lean_inc(x_73);
lean_inc(x_99);
x_102 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3), 9, 4);
lean_closure_set(x_102, 0, x_99);
lean_closure_set(x_102, 1, x_73);
lean_closure_set(x_102, 2, x_101);
lean_closure_set(x_102, 3, x_25);
lean_inc(x_100);
x_103 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_100, x_102, x_6, x_7, x_8, x_9, x_78);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
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
x_106 = l_Lean_Meta_FVarSubst_get(x_99, x_73);
x_107 = l_Lean_Expr_fvarId_x21(x_106);
x_108 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_108, 0, x_100);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_108, 2, x_99);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_68);
if (lean_is_scalar(x_105)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_105;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_104);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_73);
lean_dec(x_68);
x_111 = lean_ctor_get(x_103, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_103, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_113 = x_103;
} else {
 lean_dec_ref(x_103);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_73);
lean_dec(x_68);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_115 = !lean_is_exclusive(x_76);
if (x_115 == 0)
{
return x_76;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_76, 0);
x_117 = lean_ctor_get(x_76, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_76);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_68);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_119 = !lean_is_exclusive(x_70);
if (x_119 == 0)
{
return x_70;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_70, 0);
x_121 = lean_ctor_get(x_70, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_70);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_123 = !lean_is_exclusive(x_63);
if (x_123 == 0)
{
return x_63;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_63, 0);
x_125 = lean_ctor_get(x_63, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_63);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; 
x_127 = lean_ctor_get(x_53, 0);
x_128 = lean_ctor_get(x_53, 1);
x_129 = lean_ctor_get(x_53, 2);
x_130 = lean_ctor_get(x_53, 3);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_53);
x_131 = l_Lean_assignExprMVar(x_1, x_48, x_127);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_128);
lean_ctor_set(x_133, 2, x_129);
lean_ctor_set(x_133, 3, x_130);
x_134 = lean_st_ref_set(x_7, x_133, x_54);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = l_Lean_Expr_mvarId_x21(x_35);
lean_dec(x_35);
x_137 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_138 = l_Lean_Meta_intro1Core(x_136, x_137, x_6, x_7, x_8, x_9, x_135);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
lean_inc(x_5);
x_143 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
lean_ctor_set(x_143, 2, x_5);
x_144 = l_Lean_Expr_mvarId_x21(x_32);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_145 = l_Lean_Meta_intro1Core(x_144, x_137, x_6, x_7, x_8, x_9, x_140);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec(x_146);
x_150 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_148);
x_151 = l_Lean_Meta_substCore(x_149, x_148, x_150, x_5, x_150, x_150, x_6, x_7, x_8, x_9, x_147);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_156 = x_152;
} else {
 lean_dec_ref(x_152);
 x_156 = lean_box(0);
}
x_157 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__11;
lean_inc(x_148);
lean_inc(x_154);
x_158 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3), 9, 4);
lean_closure_set(x_158, 0, x_154);
lean_closure_set(x_158, 1, x_148);
lean_closure_set(x_158, 2, x_157);
lean_closure_set(x_158, 3, x_25);
lean_inc(x_155);
x_159 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_155, x_158, x_6, x_7, x_8, x_9, x_153);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_161 = x_159;
} else {
 lean_dec_ref(x_159);
 x_161 = lean_box(0);
}
x_162 = l_Lean_Meta_FVarSubst_get(x_154, x_148);
x_163 = l_Lean_Expr_fvarId_x21(x_162);
x_164 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_164, 0, x_155);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_164, 2, x_154);
if (lean_is_scalar(x_156)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_156;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_143);
if (lean_is_scalar(x_161)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_161;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_160);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_148);
lean_dec(x_143);
x_167 = lean_ctor_get(x_159, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_159, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_169 = x_159;
} else {
 lean_dec_ref(x_159);
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
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_148);
lean_dec(x_143);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_171 = lean_ctor_get(x_151, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_151, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_173 = x_151;
} else {
 lean_dec_ref(x_151);
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
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_143);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_175 = lean_ctor_get(x_145, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_145, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_177 = x_145;
} else {
 lean_dec_ref(x_145);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_179 = lean_ctor_get(x_138, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_138, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_181 = x_138;
} else {
 lean_dec_ref(x_138);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_183 = !lean_is_exclusive(x_47);
if (x_183 == 0)
{
return x_47;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_47, 0);
x_185 = lean_ctor_get(x_47, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_47);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_187 = !lean_is_exclusive(x_22);
if (x_187 == 0)
{
return x_22;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_22, 0);
x_189 = lean_ctor_get(x_22, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_22);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_191 = !lean_is_exclusive(x_17);
if (x_191 == 0)
{
return x_17;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_17, 0);
x_193 = lean_ctor_get(x_17, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_17);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_195 = !lean_is_exclusive(x_15);
if (x_195 == 0)
{
return x_15;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_15, 0);
x_197 = lean_ctor_get(x_15, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_15);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_11);
if (x_199 == 0)
{
return x_11;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_11, 0);
x_201 = lean_ctor_get(x_11, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_11);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___boxed), 10, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
x_12 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("h", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValue___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("thenBranch", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValue___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elseBranch", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValue___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = l_Lean_Meta_caseValue___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux(x_1, x_2, x_3, x_10, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Meta_caseValue___closed__4;
x_17 = l_Lean_Meta_appendTagSuffix(x_15, x_16, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Meta_caseValue___closed__6;
x_22 = l_Lean_Meta_appendTagSuffix(x_20, x_21, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_12);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_11);
if (x_35 == 0)
{
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_11, 0);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_Meta_CaseValuesSubgoal_newHs___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_CaseValuesSubgoal_newHs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_CaseValuesSubgoal_newHs___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CaseValuesSubgoal_subst___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Meta_CaseValuesSubgoal_newHs___default___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCaseValuesSubgoal() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_caseValues_loop___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_19; lean_object* x_20; 
x_12 = lean_array_uget(x_2, x_3);
x_19 = lean_ctor_get(x_1, 2);
x_20 = l_Lean_Meta_FVarSubst_get(x_19, x_12);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Meta_tryClear(x_5, x_21, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_13 = x_23;
x_14 = x_24;
goto block_18;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_dec(x_20);
x_13 = x_5;
x_14 = x_10;
goto block_18;
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_5 = x_13;
x_10 = x_14;
goto _start;
}
}
else
{
lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
lean_dec(x_7);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_20 = lean_name_append_index_after(x_4, x_19);
lean_inc(x_16);
x_21 = l_Lean_Meta_appendTagSuffix(x_16, x_20, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_array_push(x_5, x_17);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_6);
x_26 = lean_array_push(x_10, x_25);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_array_push(x_5, x_17);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_6);
x_30 = lean_array_push(x_10, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_6);
lean_dec(x_4);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_3, x_36);
lean_dec(x_3);
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_dec(x_2);
x_40 = lean_array_push(x_5, x_39);
x_41 = l_Lean_Meta_caseValues_loop(x_7, x_8, x_9, x_37, x_38, x_1, x_40, x_10, x_11, x_12, x_13, x_14, x_15);
return x_41;
}
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("caseValues", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValues_loop___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("list of values must not be empty", 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValues_loop___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValues_loop___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("case", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValues_loop___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues_loop(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Meta_caseValues_loop___closed__2;
x_15 = l_Lean_Meta_caseValues_loop___closed__5;
x_16 = l_Lean_Meta_throwTacticEx___rarg(x_14, x_5, x_15, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
lean_inc(x_4);
lean_inc(x_2);
x_19 = lean_name_append_index_after(x_2, x_4);
x_20 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_21 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux(x_5, x_1, x_17, x_19, x_20, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 2);
lean_inc(x_28);
x_29 = l_Lean_Meta_caseValues_loop___closed__7;
lean_inc(x_4);
x_30 = lean_name_append_index_after(x_29, x_4);
lean_inc(x_26);
x_31 = l_Lean_Meta_appendTagSuffix(x_26, x_30, x_9, x_10, x_11, x_12, x_24);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_array_get_size(x_7);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_lt(x_34, x_33);
if (x_35 == 0)
{
lean_dec(x_33);
lean_dec(x_23);
x_36 = x_26;
x_37 = x_32;
goto block_58;
}
else
{
uint8_t x_59; 
x_59 = lean_nat_dec_le(x_33, x_33);
if (x_59 == 0)
{
lean_dec(x_33);
lean_dec(x_23);
x_36 = x_26;
x_37 = x_32;
goto block_58;
}
else
{
size_t x_60; size_t x_61; lean_object* x_62; 
x_60 = 0;
x_61 = lean_usize_of_nat(x_33);
lean_dec(x_33);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_62 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_caseValues_loop___spec__1(x_23, x_7, x_60, x_61, x_26, x_9, x_10, x_11, x_12, x_32);
lean_dec(x_23);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_36 = x_63;
x_37 = x_64;
goto block_58;
}
else
{
uint8_t x_65; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_62, 0);
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_62);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
block_58:
{
if (x_3 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = l_Lean_Meta_caseValues_loop___closed__8;
x_39 = lean_array_push(x_38, x_27);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_28);
x_41 = lean_array_push(x_8, x_40);
x_42 = l_Lean_Meta_caseValues_loop___lambda__1(x_18, x_25, x_4, x_29, x_7, x_20, x_1, x_2, x_3, x_41, x_9, x_10, x_11, x_12, x_37);
return x_42;
}
else
{
uint8_t x_43; uint8_t x_44; lean_object* x_45; 
x_43 = 0;
x_44 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_45 = l_Lean_Meta_substCore(x_36, x_27, x_43, x_28, x_44, x_43, x_9, x_10, x_11, x_12, x_37);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = l_Lean_Meta_CaseValuesSubgoal_newHs___default___closed__1;
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_48);
x_52 = lean_array_push(x_8, x_51);
x_53 = l_Lean_Meta_caseValues_loop___lambda__1(x_18, x_25, x_4, x_29, x_7, x_20, x_1, x_2, x_3, x_52, x_9, x_10, x_11, x_12, x_47);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_45);
if (x_54 == 0)
{
return x_45;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_45, 0);
x_56 = lean_ctor_get(x_45, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_45);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_31);
if (x_69 == 0)
{
return x_31;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_31, 0);
x_71 = lean_ctor_get(x_31, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_31);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_21);
if (x_73 == 0)
{
return x_21;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_21, 0);
x_75 = lean_ctor_get(x_21, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_21);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_caseValues_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_caseValues_loop___spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues_loop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_9);
lean_dec(x_9);
x_17 = l_Lean_Meta_caseValues_loop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Meta_caseValues_loop(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_to_list(lean_box(0), x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Meta_CaseValuesSubgoal_newHs___default___closed__1;
x_14 = l_Lean_Meta_caseValues_loop(x_2, x_4, x_5, x_12, x_1, x_11, x_13, x_13, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_caseValues(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_Value(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_CaseValues(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_Value(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_CaseValueSubgoal_subst___default = _init_l_Lean_Meta_CaseValueSubgoal_subst___default();
lean_mark_persistent(l_Lean_Meta_CaseValueSubgoal_subst___default);
l_Lean_Meta_instInhabitedCaseValueSubgoal___closed__1 = _init_l_Lean_Meta_instInhabitedCaseValueSubgoal___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedCaseValueSubgoal___closed__1);
l_Lean_Meta_instInhabitedCaseValueSubgoal = _init_l_Lean_Meta_instInhabitedCaseValueSubgoal();
lean_mark_persistent(l_Lean_Meta_instInhabitedCaseValueSubgoal);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1___closed__1 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1___closed__1);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1___closed__2 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1___closed__2);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2___closed__1 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2___closed__1);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2___closed__2 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2___closed__2);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__1 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__1);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__2 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__2);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__3 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__3);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__4 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__4);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__1 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__1);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__2 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__2);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__3 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__3);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__4 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__4);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__5 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__5);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__6 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__6);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__7 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__7);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__8 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__8);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__9 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__9);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__10 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__10);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__11 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__11);
l_Lean_Meta_caseValue___closed__1 = _init_l_Lean_Meta_caseValue___closed__1();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__1);
l_Lean_Meta_caseValue___closed__2 = _init_l_Lean_Meta_caseValue___closed__2();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__2);
l_Lean_Meta_caseValue___closed__3 = _init_l_Lean_Meta_caseValue___closed__3();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__3);
l_Lean_Meta_caseValue___closed__4 = _init_l_Lean_Meta_caseValue___closed__4();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__4);
l_Lean_Meta_caseValue___closed__5 = _init_l_Lean_Meta_caseValue___closed__5();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__5);
l_Lean_Meta_caseValue___closed__6 = _init_l_Lean_Meta_caseValue___closed__6();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__6);
l_Lean_Meta_CaseValuesSubgoal_newHs___default___closed__1 = _init_l_Lean_Meta_CaseValuesSubgoal_newHs___default___closed__1();
lean_mark_persistent(l_Lean_Meta_CaseValuesSubgoal_newHs___default___closed__1);
l_Lean_Meta_CaseValuesSubgoal_newHs___default = _init_l_Lean_Meta_CaseValuesSubgoal_newHs___default();
lean_mark_persistent(l_Lean_Meta_CaseValuesSubgoal_newHs___default);
l_Lean_Meta_CaseValuesSubgoal_subst___default = _init_l_Lean_Meta_CaseValuesSubgoal_subst___default();
lean_mark_persistent(l_Lean_Meta_CaseValuesSubgoal_subst___default);
l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__1 = _init_l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__1);
l_Lean_Meta_instInhabitedCaseValuesSubgoal = _init_l_Lean_Meta_instInhabitedCaseValuesSubgoal();
lean_mark_persistent(l_Lean_Meta_instInhabitedCaseValuesSubgoal);
l_Lean_Meta_caseValues_loop___closed__1 = _init_l_Lean_Meta_caseValues_loop___closed__1();
lean_mark_persistent(l_Lean_Meta_caseValues_loop___closed__1);
l_Lean_Meta_caseValues_loop___closed__2 = _init_l_Lean_Meta_caseValues_loop___closed__2();
lean_mark_persistent(l_Lean_Meta_caseValues_loop___closed__2);
l_Lean_Meta_caseValues_loop___closed__3 = _init_l_Lean_Meta_caseValues_loop___closed__3();
lean_mark_persistent(l_Lean_Meta_caseValues_loop___closed__3);
l_Lean_Meta_caseValues_loop___closed__4 = _init_l_Lean_Meta_caseValues_loop___closed__4();
lean_mark_persistent(l_Lean_Meta_caseValues_loop___closed__4);
l_Lean_Meta_caseValues_loop___closed__5 = _init_l_Lean_Meta_caseValues_loop___closed__5();
lean_mark_persistent(l_Lean_Meta_caseValues_loop___closed__5);
l_Lean_Meta_caseValues_loop___closed__6 = _init_l_Lean_Meta_caseValues_loop___closed__6();
lean_mark_persistent(l_Lean_Meta_caseValues_loop___closed__6);
l_Lean_Meta_caseValues_loop___closed__7 = _init_l_Lean_Meta_caseValues_loop___closed__7();
lean_mark_persistent(l_Lean_Meta_caseValues_loop___closed__7);
l_Lean_Meta_caseValues_loop___closed__8 = _init_l_Lean_Meta_caseValues_loop___closed__8();
lean_mark_persistent(l_Lean_Meta_caseValues_loop___closed__8);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
