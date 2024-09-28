// Lean compiler output
// Module: Lean.Meta.Match.CaseValues
// Imports: Lean.Meta.Tactic.Subst Lean.Meta.Tactic.Clear Lean.Meta.Match.Value
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
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValues_loop___closed__6;
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__2;
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1___closed__2;
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValue___closed__6;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__7;
lean_object* l_Lean_Meta_normLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2___closed__2;
static lean_object* l_Lean_Meta_caseValues_loop___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2___closed__1;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__4;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValues_loop___closed__2;
static lean_object* l_Lean_Meta_caseValue___closed__5;
static lean_object* l_Lean_Meta_caseValues_loop___closed__3;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__3;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_appendTagSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValues_loop___closed__1;
static lean_object* l_Lean_Meta_CaseValuesSubgoal_newHs___default___closed__1;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__1;
static lean_object* l_Lean_Meta_caseValue___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__9;
static lean_object* l_Lean_Meta_caseValues_loop___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_CaseValueSubgoal_subst___default;
static lean_object* l_Lean_Meta_caseValue___closed__3;
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__1;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_caseValues_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedCaseValueSubgoal___closed__1;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues_loop(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CaseValuesSubgoal_newHs___default;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValues_loop___closed__4;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__2;
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_domain(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_CaseValuesSubgoal_subst___default;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__8;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1___closed__1;
static lean_object* l_Lean_Meta_caseValues_loop___closed__7;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedCaseValueSubgoal;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_compileDecl___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValue___closed__4;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_caseValues_loop___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValue___closed__2;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedCaseValuesSubgoal;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__2;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_1 = lean_mk_string_unchecked("found decl", 10, 10);
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
x_9 = l_Lean_FVarId_getDecl(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_2);
x_11 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_2, x_4, x_5, x_6, x_7, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_4);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1___closed__2;
x_22 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_2, x_21, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_4);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_4);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("searching for decl", 18, 18);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_Meta_FVarSubst_get(x_1, x_2);
x_11 = l_Lean_Expr_fvarId_x21(x_10);
lean_dec(x_10);
lean_inc(x_3);
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_5, x_6, x_7, x_8, x_9);
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
x_17 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1(x_11, x_3, x_16, x_5, x_6, x_7, x_8, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2___closed__2;
lean_inc(x_3);
x_20 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_3, x_19, x_5, x_6, x_7, x_8, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__1(x_11, x_3, x_21, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_21);
return x_23;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subst domain: ", 14, 14);
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
x_1 = lean_mk_string_unchecked("", 0, 0);
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box(0);
x_15 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2(x_2, x_3, x_1, x_14, x_5, x_6, x_7, x_8, x_13);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_19 = l_Lean_Meta_FVarSubst_domain(x_2);
lean_inc(x_4);
x_20 = l_List_mapTR_loop___at___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___spec__1(x_19, x_4);
x_21 = l_List_mapTR_loop___at_Lean_compileDecl___spec__1(x_20, x_4);
x_22 = l_Lean_MessageData_ofList(x_21);
x_23 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__2;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_23);
x_24 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__4;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_1);
x_26 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_1, x_25, x_5, x_6, x_7, x_8, x_17);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2(x_2, x_3, x_1, x_27, x_5, x_6, x_7, x_8, x_28);
lean_dec(x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_dec(x_10);
x_31 = l_Lean_Meta_FVarSubst_domain(x_2);
lean_inc(x_4);
x_32 = l_List_mapTR_loop___at___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___spec__1(x_31, x_4);
x_33 = l_List_mapTR_loop___at_Lean_compileDecl___spec__1(x_32, x_4);
x_34 = l_Lean_MessageData_ofList(x_33);
x_35 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__2;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___closed__4;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_1);
x_39 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_1, x_38, x_5, x_6, x_7, x_8, x_30);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2(x_2, x_3, x_1, x_40, x_5, x_6, x_7, x_8, x_41);
lean_dec(x_40);
return x_42;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("caseValue", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dite", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_MVarId_getTag(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__2;
lean_inc(x_1);
x_15 = l_Lean_MVarId_checkNotAssigned(x_1, x_14, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_1);
x_17 = l_Lean_MVarId_getType(x_1, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Meta_normLitValue(x_2, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_fvar___override(x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Meta_mkEq(x_23, x_21, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__5;
lean_inc(x_25);
x_29 = l_Lean_Expr_app___override(x_28, x_25);
x_30 = 0;
lean_inc(x_18);
lean_inc(x_25);
lean_inc(x_4);
x_31 = l_Lean_Expr_forallE___override(x_4, x_25, x_18, x_30);
x_32 = l_Lean_Expr_forallE___override(x_4, x_29, x_18, x_30);
lean_inc(x_6);
lean_inc(x_12);
x_33 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_31, x_12, x_6, x_7, x_8, x_9, x_26);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_6);
x_37 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_32, x_12, x_6, x_7, x_8, x_9, x_36);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_25);
lean_inc(x_35);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_35);
lean_inc(x_39);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set(x_37, 0, x_44);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 1, x_37);
lean_ctor_set(x_33, 0, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_33);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_array_mk(x_47);
x_49 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__7;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_50 = l_Lean_Meta_mkAppOptM(x_49, x_48, x_6, x_7, x_8, x_9, x_40);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_51, x_6, x_7, x_8, x_9, x_52);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_Lean_Expr_mvarId_x21(x_39);
lean_dec(x_39);
x_56 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_57 = l_Lean_Meta_intro1Core(x_55, x_56, x_6, x_7, x_8, x_9, x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
lean_inc(x_5);
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
lean_ctor_set(x_62, 2, x_5);
x_63 = l_Lean_Expr_mvarId_x21(x_35);
lean_dec(x_35);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_64 = l_Lean_Meta_intro1Core(x_63, x_56, x_6, x_7, x_8, x_9, x_59);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_67);
x_70 = l_Lean_Meta_substCore(x_68, x_67, x_69, x_5, x_69, x_69, x_6, x_7, x_8, x_9, x_66);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_71, 0);
x_75 = lean_ctor_get(x_71, 1);
x_76 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__9;
lean_inc(x_67);
lean_inc(x_74);
x_77 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___boxed), 9, 4);
lean_closure_set(x_77, 0, x_76);
lean_closure_set(x_77, 1, x_74);
lean_closure_set(x_77, 2, x_67);
lean_closure_set(x_77, 3, x_27);
lean_inc(x_75);
x_78 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_75, x_77, x_6, x_7, x_8, x_9, x_72);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_78, 0);
lean_dec(x_80);
x_81 = l_Lean_Meta_FVarSubst_get(x_74, x_67);
x_82 = l_Lean_Expr_fvarId_x21(x_81);
lean_dec(x_81);
x_83 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_83, 0, x_75);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_74);
lean_ctor_set(x_71, 1, x_62);
lean_ctor_set(x_71, 0, x_83);
lean_ctor_set(x_78, 0, x_71);
return x_78;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_78, 1);
lean_inc(x_84);
lean_dec(x_78);
x_85 = l_Lean_Meta_FVarSubst_get(x_74, x_67);
x_86 = l_Lean_Expr_fvarId_x21(x_85);
lean_dec(x_85);
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_75);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_74);
lean_ctor_set(x_71, 1, x_62);
lean_ctor_set(x_71, 0, x_87);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_71);
lean_ctor_set(x_88, 1, x_84);
return x_88;
}
}
else
{
uint8_t x_89; 
lean_free_object(x_71);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_67);
lean_dec(x_62);
x_89 = !lean_is_exclusive(x_78);
if (x_89 == 0)
{
return x_78;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_78, 0);
x_91 = lean_ctor_get(x_78, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_78);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_71, 0);
x_94 = lean_ctor_get(x_71, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_71);
x_95 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__9;
lean_inc(x_67);
lean_inc(x_93);
x_96 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___boxed), 9, 4);
lean_closure_set(x_96, 0, x_95);
lean_closure_set(x_96, 1, x_93);
lean_closure_set(x_96, 2, x_67);
lean_closure_set(x_96, 3, x_27);
lean_inc(x_94);
x_97 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_94, x_96, x_6, x_7, x_8, x_9, x_72);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = l_Lean_Meta_FVarSubst_get(x_93, x_67);
x_101 = l_Lean_Expr_fvarId_x21(x_100);
lean_dec(x_100);
x_102 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_102, 0, x_94);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_102, 2, x_93);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_62);
if (lean_is_scalar(x_99)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_99;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_98);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_67);
lean_dec(x_62);
x_105 = lean_ctor_get(x_97, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_97, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_107 = x_97;
} else {
 lean_dec_ref(x_97);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_67);
lean_dec(x_62);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_109 = !lean_is_exclusive(x_70);
if (x_109 == 0)
{
return x_70;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_70, 0);
x_111 = lean_ctor_get(x_70, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_70);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_62);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_113 = !lean_is_exclusive(x_64);
if (x_113 == 0)
{
return x_64;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_64, 0);
x_115 = lean_ctor_get(x_64, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_64);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_117 = !lean_is_exclusive(x_57);
if (x_117 == 0)
{
return x_57;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_57, 0);
x_119 = lean_ctor_get(x_57, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_57);
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
lean_dec(x_39);
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_50);
if (x_121 == 0)
{
return x_50;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_50, 0);
x_123 = lean_ctor_get(x_50, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_50);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_125 = lean_ctor_get(x_37, 0);
x_126 = lean_ctor_get(x_37, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_37);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_25);
lean_inc(x_35);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_35);
lean_inc(x_125);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_125);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_27);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 1, x_131);
lean_ctor_set(x_33, 0, x_129);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_33);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_128);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_127);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_array_mk(x_134);
x_136 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__7;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_137 = l_Lean_Meta_mkAppOptM(x_136, x_135, x_6, x_7, x_8, x_9, x_126);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_138, x_6, x_7, x_8, x_9, x_139);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = l_Lean_Expr_mvarId_x21(x_125);
lean_dec(x_125);
x_143 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_144 = l_Lean_Meta_intro1Core(x_142, x_143, x_6, x_7, x_8, x_9, x_141);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
lean_inc(x_5);
x_149 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
lean_ctor_set(x_149, 2, x_5);
x_150 = l_Lean_Expr_mvarId_x21(x_35);
lean_dec(x_35);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_151 = l_Lean_Meta_intro1Core(x_150, x_143, x_6, x_7, x_8, x_9, x_146);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_dec(x_152);
x_156 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_154);
x_157 = l_Lean_Meta_substCore(x_155, x_154, x_156, x_5, x_156, x_156, x_6, x_7, x_8, x_9, x_153);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_162 = x_158;
} else {
 lean_dec_ref(x_158);
 x_162 = lean_box(0);
}
x_163 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__9;
lean_inc(x_154);
lean_inc(x_160);
x_164 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___boxed), 9, 4);
lean_closure_set(x_164, 0, x_163);
lean_closure_set(x_164, 1, x_160);
lean_closure_set(x_164, 2, x_154);
lean_closure_set(x_164, 3, x_27);
lean_inc(x_161);
x_165 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_161, x_164, x_6, x_7, x_8, x_9, x_159);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
x_168 = l_Lean_Meta_FVarSubst_get(x_160, x_154);
x_169 = l_Lean_Expr_fvarId_x21(x_168);
lean_dec(x_168);
x_170 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_170, 0, x_161);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set(x_170, 2, x_160);
if (lean_is_scalar(x_162)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_162;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_149);
if (lean_is_scalar(x_167)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_167;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_166);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_154);
lean_dec(x_149);
x_173 = lean_ctor_get(x_165, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_165, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_175 = x_165;
} else {
 lean_dec_ref(x_165);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_177 = lean_ctor_get(x_157, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_157, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_179 = x_157;
} else {
 lean_dec_ref(x_157);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_149);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_181 = lean_ctor_get(x_151, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_151, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_183 = x_151;
} else {
 lean_dec_ref(x_151);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_185 = lean_ctor_get(x_144, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_144, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_187 = x_144;
} else {
 lean_dec_ref(x_144);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_125);
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_189 = lean_ctor_get(x_137, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_137, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_191 = x_137;
} else {
 lean_dec_ref(x_137);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_193 = lean_ctor_get(x_33, 0);
x_194 = lean_ctor_get(x_33, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_33);
lean_inc(x_6);
x_195 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_32, x_12, x_6, x_7, x_8, x_9, x_194);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_198 = x_195;
} else {
 lean_dec_ref(x_195);
 x_198 = lean_box(0);
}
x_199 = lean_box(0);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_25);
lean_inc(x_193);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_193);
lean_inc(x_196);
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_196);
if (lean_is_scalar(x_198)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_198;
 lean_ctor_set_tag(x_203, 1);
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_27);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_199);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_200);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_199);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_array_mk(x_207);
x_209 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__7;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_210 = l_Lean_Meta_mkAppOptM(x_209, x_208, x_6, x_7, x_8, x_9, x_197);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_213 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_211, x_6, x_7, x_8, x_9, x_212);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
x_215 = l_Lean_Expr_mvarId_x21(x_196);
lean_dec(x_196);
x_216 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_217 = l_Lean_Meta_intro1Core(x_215, x_216, x_6, x_7, x_8, x_9, x_214);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = lean_ctor_get(x_218, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec(x_218);
lean_inc(x_5);
x_222 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_220);
lean_ctor_set(x_222, 2, x_5);
x_223 = l_Lean_Expr_mvarId_x21(x_193);
lean_dec(x_193);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_224 = l_Lean_Meta_intro1Core(x_223, x_216, x_6, x_7, x_8, x_9, x_219);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = lean_ctor_get(x_225, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_225, 1);
lean_inc(x_228);
lean_dec(x_225);
x_229 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_227);
x_230 = l_Lean_Meta_substCore(x_228, x_227, x_229, x_5, x_229, x_229, x_6, x_7, x_8, x_9, x_226);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_ctor_get(x_231, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_231, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_235 = x_231;
} else {
 lean_dec_ref(x_231);
 x_235 = lean_box(0);
}
x_236 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4___closed__9;
lean_inc(x_227);
lean_inc(x_233);
x_237 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___boxed), 9, 4);
lean_closure_set(x_237, 0, x_236);
lean_closure_set(x_237, 1, x_233);
lean_closure_set(x_237, 2, x_227);
lean_closure_set(x_237, 3, x_27);
lean_inc(x_234);
x_238 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_234, x_237, x_6, x_7, x_8, x_9, x_232);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_240 = x_238;
} else {
 lean_dec_ref(x_238);
 x_240 = lean_box(0);
}
x_241 = l_Lean_Meta_FVarSubst_get(x_233, x_227);
x_242 = l_Lean_Expr_fvarId_x21(x_241);
lean_dec(x_241);
x_243 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_243, 0, x_234);
lean_ctor_set(x_243, 1, x_242);
lean_ctor_set(x_243, 2, x_233);
if (lean_is_scalar(x_235)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_235;
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_222);
if (lean_is_scalar(x_240)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_240;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_239);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_227);
lean_dec(x_222);
x_246 = lean_ctor_get(x_238, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_238, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_248 = x_238;
} else {
 lean_dec_ref(x_238);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_227);
lean_dec(x_222);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_250 = lean_ctor_get(x_230, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_230, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_252 = x_230;
} else {
 lean_dec_ref(x_230);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_222);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_254 = lean_ctor_get(x_224, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_224, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_256 = x_224;
} else {
 lean_dec_ref(x_224);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_193);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_258 = lean_ctor_get(x_217, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_217, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_260 = x_217;
} else {
 lean_dec_ref(x_217);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_196);
lean_dec(x_193);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_262 = lean_ctor_get(x_210, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_210, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_264 = x_210;
} else {
 lean_dec_ref(x_210);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_266 = !lean_is_exclusive(x_24);
if (x_266 == 0)
{
return x_24;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_24, 0);
x_268 = lean_ctor_get(x_24, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_24);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
else
{
uint8_t x_270; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_270 = !lean_is_exclusive(x_20);
if (x_270 == 0)
{
return x_20;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_20, 0);
x_272 = lean_ctor_get(x_20, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_20);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
return x_273;
}
}
}
else
{
uint8_t x_274; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_274 = !lean_is_exclusive(x_17);
if (x_274 == 0)
{
return x_17;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_17, 0);
x_276 = lean_ctor_get(x_17, 1);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_17);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
return x_277;
}
}
}
else
{
uint8_t x_278; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_278 = !lean_is_exclusive(x_15);
if (x_278 == 0)
{
return x_15;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_15, 0);
x_280 = lean_ctor_get(x_15, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_15);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
return x_281;
}
}
}
else
{
uint8_t x_282; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_282 = !lean_is_exclusive(x_11);
if (x_282 == 0)
{
return x_11;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_11, 0);
x_284 = lean_ctor_get(x_11, 1);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_11);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
return x_285;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__4), 10, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
x_12 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_11, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValue___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("thenBranch", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValue___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elseBranch", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValue___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
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
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__1;
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
x_1 = l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__2;
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
x_22 = l_Lean_MVarId_tryClear(x_5, x_21, x_6, x_7, x_8, x_9, x_10);
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
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
lean_dec(x_19);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_3, x_20);
x_22 = lean_name_append_index_after(x_4, x_21);
lean_inc(x_17);
x_23 = l_Lean_Meta_appendTagSuffix(x_17, x_22, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_array_push(x_5, x_18);
lean_ctor_set(x_2, 2, x_6);
lean_ctor_set(x_2, 1, x_26);
x_27 = lean_array_push(x_10, x_2);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_array_push(x_5, x_18);
lean_ctor_set(x_2, 2, x_6);
lean_ctor_set(x_2, 1, x_29);
x_30 = lean_array_push(x_10, x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_free_object(x_2);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_23);
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
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_2);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_3, x_38);
x_40 = lean_name_append_index_after(x_4, x_39);
lean_inc(x_36);
x_41 = l_Lean_Meta_appendTagSuffix(x_36, x_40, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_array_push(x_5, x_37);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_6);
x_46 = lean_array_push(x_10, x_45);
if (lean_is_scalar(x_43)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_43;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_48 = lean_ctor_get(x_41, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_50 = x_41;
} else {
 lean_dec_ref(x_41);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_6);
lean_dec(x_4);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_3, x_52);
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
lean_dec(x_2);
x_56 = lean_array_push(x_5, x_55);
x_57 = l_Lean_Meta_caseValues_loop(x_7, x_8, x_9, x_53, x_54, x_1, x_56, x_10, x_11, x_12, x_13, x_14, x_15);
return x_57;
}
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("caseValues", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValues_loop___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("list of values must not be empty", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValues_loop___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValues_loop___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValues_loop___closed__5;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("case", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValues_loop___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
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
x_15 = l_Lean_Meta_caseValues_loop___closed__6;
x_16 = l_Lean_Meta_throwTacticEx___rarg(x_14, x_5, x_15, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_19 = x_6;
} else {
 lean_dec_ref(x_6);
 x_19 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_2);
x_20 = lean_name_append_index_after(x_2, x_4);
x_21 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_22 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux(x_5, x_1, x_17, x_20, x_21, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 2);
lean_inc(x_29);
x_30 = l_Lean_Meta_caseValues_loop___closed__8;
lean_inc(x_4);
x_31 = lean_name_append_index_after(x_30, x_4);
lean_inc(x_27);
x_32 = l_Lean_Meta_appendTagSuffix(x_27, x_31, x_9, x_10, x_11, x_12, x_25);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_array_get_size(x_7);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_lt(x_35, x_34);
if (x_36 == 0)
{
lean_dec(x_34);
lean_dec(x_24);
x_37 = x_27;
x_38 = x_33;
goto block_60;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_34, x_34);
if (x_61 == 0)
{
lean_dec(x_34);
lean_dec(x_24);
x_37 = x_27;
x_38 = x_33;
goto block_60;
}
else
{
size_t x_62; size_t x_63; lean_object* x_64; 
x_62 = 0;
x_63 = lean_usize_of_nat(x_34);
lean_dec(x_34);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_64 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_caseValues_loop___spec__1(x_24, x_7, x_62, x_63, x_27, x_9, x_10, x_11, x_12, x_33);
lean_dec(x_24);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_37 = x_65;
x_38 = x_66;
goto block_60;
}
else
{
uint8_t x_67; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_19);
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
x_67 = !lean_is_exclusive(x_64);
if (x_67 == 0)
{
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 0);
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_64);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
block_60:
{
if (x_3 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_box(0);
if (lean_is_scalar(x_19)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_19;
}
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_array_mk(x_40);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_29);
x_43 = lean_array_push(x_8, x_42);
x_44 = l_Lean_Meta_caseValues_loop___lambda__1(x_18, x_26, x_4, x_30, x_7, x_21, x_1, x_2, x_3, x_43, x_9, x_10, x_11, x_12, x_38);
lean_dec(x_4);
return x_44;
}
else
{
uint8_t x_45; uint8_t x_46; lean_object* x_47; 
lean_dec(x_19);
x_45 = 0;
x_46 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_47 = l_Lean_Meta_substCore(x_37, x_28, x_45, x_29, x_46, x_45, x_9, x_10, x_11, x_12, x_38);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l_Lean_Meta_CaseValuesSubgoal_newHs___default___closed__1;
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_50);
x_54 = lean_array_push(x_8, x_53);
x_55 = l_Lean_Meta_caseValues_loop___lambda__1(x_18, x_26, x_4, x_30, x_7, x_21, x_1, x_2, x_3, x_54, x_9, x_10, x_11, x_12, x_49);
lean_dec(x_4);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_26);
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
x_56 = !lean_is_exclusive(x_47);
if (x_56 == 0)
{
return x_47;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_47, 0);
x_58 = lean_ctor_get(x_47, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_47);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_19);
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
x_71 = !lean_is_exclusive(x_32);
if (x_71 == 0)
{
return x_32;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_32, 0);
x_73 = lean_ctor_get(x_32, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_32);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_19);
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
x_75 = !lean_is_exclusive(x_22);
if (x_75 == 0)
{
return x_22;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_22, 0);
x_77 = lean_ctor_get(x_22, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_22);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
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
lean_dec(x_3);
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
x_11 = lean_array_to_list(x_3);
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
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_Value(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_CaseValues(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__2 = _init_l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__2);
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
