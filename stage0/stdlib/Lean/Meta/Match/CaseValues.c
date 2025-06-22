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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValues_loop___closed__6;
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__8;
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValues_loop___closed__9;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_caseValues_loop_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__6;
lean_object* l_Lean_Meta_normLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__0;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__4;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValues_loop___closed__5;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedCaseValueSubgoal___closed__0;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__3;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
static lean_object* l_Lean_Meta_caseValues_loop___closed__2;
static lean_object* l_Lean_Meta_caseValue___closed__5;
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValues_loop___closed__3;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__7;
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__10;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__1;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_appendTagSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValues_loop___closed__1;
static lean_object* l_Lean_Meta_caseValue___closed__1;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__0;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__9;
static lean_object* l_Lean_Meta_caseValues_loop___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValues_loop___closed__8;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__7;
static lean_object* l_Lean_Meta_caseValue___closed__3;
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__5;
static lean_object* l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__1;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValue___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseValues_loop(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__3;
static lean_object* l_Lean_Meta_caseValues_loop___closed__4;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_domain(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__0;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__6;
lean_object* l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValues_loop___closed__7;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedCaseValueSubgoal;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValue___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_caseValues_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseValue___closed__2;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__4;
static lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedCaseValuesSubgoal;
static lean_object* _init_l_Lean_Meta_instInhabitedCaseValueSubgoal___closed__0() {
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
x_1 = l_Lean_Meta_instInhabitedCaseValueSubgoal___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
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
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("found decl", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("searching for decl", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subst domain: ", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_inc(x_1);
x_49 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_1, x_6, x_8);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_52;
goto block_48;
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_54 = lean_ctor_get(x_49, 1);
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
x_56 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__5;
x_57 = l_Lean_Meta_FVarSubst_domain(x_2);
x_58 = lean_box(0);
x_59 = l_List_mapTR_loop___at_____private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux_spec__0(x_57, x_58);
x_60 = lean_box(0);
x_61 = l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(x_59, x_60);
x_62 = l_Lean_MessageData_ofList(x_61);
lean_ctor_set_tag(x_49, 7);
lean_ctor_set(x_49, 1, x_62);
lean_ctor_set(x_49, 0, x_56);
x_63 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__7;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_49);
lean_ctor_set(x_64, 1, x_63);
lean_inc(x_1);
x_65 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_1, x_64, x_4, x_5, x_6, x_7, x_54);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_66;
goto block_48;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
lean_dec(x_49);
x_68 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__5;
x_69 = l_Lean_Meta_FVarSubst_domain(x_2);
x_70 = lean_box(0);
x_71 = l_List_mapTR_loop___at_____private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux_spec__0(x_69, x_70);
x_72 = lean_box(0);
x_73 = l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(x_71, x_72);
x_74 = l_Lean_MessageData_ofList(x_73);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_68);
lean_ctor_set(x_75, 1, x_74);
x_76 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__7;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
lean_inc(x_1);
x_78 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_1, x_77, x_4, x_5, x_6, x_7, x_67);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_79;
goto block_48;
}
}
block_33:
{
lean_object* x_15; 
lean_inc(x_10);
x_15 = l_Lean_FVarId_getDecl___redArg(x_9, x_10, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_1);
x_17 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_1, x_12, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__1;
x_28 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_1, x_27, x_10, x_11, x_12, x_13, x_26);
lean_dec(x_10);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
block_48:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_inc(x_1);
x_39 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_1, x_36, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_FVarSubst_get(x_2, x_3);
x_43 = l_Lean_Expr_fvarId_x21(x_42);
lean_dec(x_42);
x_44 = lean_unbox(x_40);
lean_dec(x_40);
if (x_44 == 0)
{
x_9 = x_43;
x_10 = x_34;
x_11 = x_35;
x_12 = x_36;
x_13 = x_37;
x_14 = x_41;
goto block_33;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__3;
lean_inc(x_1);
x_46 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_1, x_45, x_34, x_35, x_36, x_37, x_41);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_9 = x_43;
x_10 = x_34;
x_11 = x_35;
x_12 = x_36;
x_13 = x_37;
x_14 = x_47;
goto block_33;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("caseValue", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dite", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__7;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_14 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__1;
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = lean_unbox(x_27);
lean_inc(x_18);
lean_inc(x_25);
lean_inc(x_4);
x_29 = l_Lean_Expr_forallE___override(x_4, x_25, x_18, x_28);
lean_inc(x_6);
lean_inc(x_12);
x_30 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_29, x_12, x_6, x_7, x_8, x_9, x_26);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__4;
lean_inc(x_25);
x_34 = l_Lean_Expr_app___override(x_33, x_25);
x_35 = lean_unbox(x_27);
x_36 = l_Lean_Expr_forallE___override(x_4, x_34, x_18, x_35);
lean_inc(x_6);
x_37 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_36, x_12, x_6, x_7, x_8, x_9, x_32);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__6;
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_25);
lean_inc(x_31);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_31);
lean_inc(x_38);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_38);
x_45 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__8;
x_46 = lean_array_push(x_45, x_42);
x_47 = lean_array_push(x_46, x_41);
x_48 = lean_array_push(x_47, x_43);
x_49 = lean_array_push(x_48, x_44);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_50 = l_Lean_Meta_mkAppOptM(x_40, x_49, x_6, x_7, x_8, x_9, x_39);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_51, x_7, x_52);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_Lean_Expr_mvarId_x21(x_38);
lean_dec(x_38);
x_56 = lean_box(1);
x_57 = lean_unbox(x_56);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_58 = l_Lean_Meta_intro1Core(x_55, x_57, x_6, x_7, x_8, x_9, x_54);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = l_Lean_Expr_mvarId_x21(x_31);
lean_dec(x_31);
x_64 = lean_unbox(x_56);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_65 = l_Lean_Meta_intro1Core(x_63, x_64, x_6, x_7, x_8, x_9, x_60);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_box(0);
x_71 = lean_unbox(x_70);
x_72 = lean_unbox(x_70);
x_73 = lean_unbox(x_70);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_68);
x_74 = l_Lean_Meta_substCore(x_69, x_68, x_71, x_5, x_72, x_73, x_6, x_7, x_8, x_9, x_67);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_75, 0);
x_79 = lean_ctor_get(x_75, 1);
x_80 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__10;
lean_inc(x_68);
lean_inc(x_78);
x_81 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___boxed), 8, 3);
lean_closure_set(x_81, 0, x_80);
lean_closure_set(x_81, 1, x_78);
lean_closure_set(x_81, 2, x_68);
lean_inc(x_79);
x_82 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_79, x_81, x_6, x_7, x_8, x_9, x_76);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_82, 0);
lean_dec(x_84);
x_85 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_85, 0, x_62);
lean_ctor_set(x_85, 1, x_61);
lean_ctor_set(x_85, 2, x_5);
x_86 = l_Lean_Meta_FVarSubst_get(x_78, x_68);
x_87 = l_Lean_Expr_fvarId_x21(x_86);
lean_dec(x_86);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_79);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_88, 2, x_78);
lean_ctor_set(x_75, 1, x_85);
lean_ctor_set(x_75, 0, x_88);
lean_ctor_set(x_82, 0, x_75);
return x_82;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_dec(x_82);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_62);
lean_ctor_set(x_90, 1, x_61);
lean_ctor_set(x_90, 2, x_5);
x_91 = l_Lean_Meta_FVarSubst_get(x_78, x_68);
x_92 = l_Lean_Expr_fvarId_x21(x_91);
lean_dec(x_91);
x_93 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_93, 0, x_79);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_78);
lean_ctor_set(x_75, 1, x_90);
lean_ctor_set(x_75, 0, x_93);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_75);
lean_ctor_set(x_94, 1, x_89);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_free_object(x_75);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_68);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_5);
x_95 = !lean_is_exclusive(x_82);
if (x_95 == 0)
{
return x_82;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_82, 0);
x_97 = lean_ctor_get(x_82, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_82);
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
x_99 = lean_ctor_get(x_75, 0);
x_100 = lean_ctor_get(x_75, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_75);
x_101 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__10;
lean_inc(x_68);
lean_inc(x_99);
x_102 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___boxed), 8, 3);
lean_closure_set(x_102, 0, x_101);
lean_closure_set(x_102, 1, x_99);
lean_closure_set(x_102, 2, x_68);
lean_inc(x_100);
x_103 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_100, x_102, x_6, x_7, x_8, x_9, x_76);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
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
x_106 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_106, 0, x_62);
lean_ctor_set(x_106, 1, x_61);
lean_ctor_set(x_106, 2, x_5);
x_107 = l_Lean_Meta_FVarSubst_get(x_99, x_68);
x_108 = l_Lean_Expr_fvarId_x21(x_107);
lean_dec(x_107);
x_109 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_109, 0, x_100);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_109, 2, x_99);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_106);
if (lean_is_scalar(x_105)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_105;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_104);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_68);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_5);
x_112 = lean_ctor_get(x_103, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_103, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_114 = x_103;
} else {
 lean_dec_ref(x_103);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_68);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_116 = !lean_is_exclusive(x_74);
if (x_116 == 0)
{
return x_74;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_74, 0);
x_118 = lean_ctor_get(x_74, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_74);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_120 = !lean_is_exclusive(x_65);
if (x_120 == 0)
{
return x_65;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_65, 0);
x_122 = lean_ctor_get(x_65, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_65);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_124 = !lean_is_exclusive(x_58);
if (x_124 == 0)
{
return x_58;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_58, 0);
x_126 = lean_ctor_get(x_58, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_58);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_38);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_50);
if (x_128 == 0)
{
return x_50;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_50, 0);
x_130 = lean_ctor_get(x_50, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_50);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_24);
if (x_132 == 0)
{
return x_24;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_24, 0);
x_134 = lean_ctor_get(x_24, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_24);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
uint8_t x_136; 
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
x_136 = !lean_is_exclusive(x_20);
if (x_136 == 0)
{
return x_20;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_20, 0);
x_138 = lean_ctor_get(x_20, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_20);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; 
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
x_140 = !lean_is_exclusive(x_17);
if (x_140 == 0)
{
return x_17;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_17, 0);
x_142 = lean_ctor_get(x_17, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_17);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
uint8_t x_144; 
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
x_144 = !lean_is_exclusive(x_15);
if (x_144 == 0)
{
return x_15;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_15, 0);
x_146 = lean_ctor_get(x_15, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_15);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_11);
if (x_148 == 0)
{
return x_11;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_11, 0);
x_150 = lean_ctor_get(x_11, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_11);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1), 10, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
x_12 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValue___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("thenBranch", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValue___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elseBranch", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValue___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValue___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Meta_caseValue___closed__1;
x_10 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux(x_1, x_2, x_3, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Meta_caseValue___closed__3;
x_18 = l_Lean_Meta_appendTagSuffix(x_16, x_17, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = l_Lean_Meta_caseValue___closed__5;
x_22 = l_Lean_Meta_appendTagSuffix(x_20, x_21, x_4, x_5, x_6, x_7, x_19);
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
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__0;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_caseValues_loop_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_eq(x_3, x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_array_uget(x_2, x_3);
x_20 = l_Lean_Meta_FVarSubst_get(x_18, x_19);
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
x_11 = x_23;
x_12 = x_24;
goto block_16;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_22;
}
}
else
{
lean_dec(x_20);
x_11 = x_5;
x_12 = x_10;
goto block_16;
}
}
else
{
lean_object* x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_11;
x_10 = x_12;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("caseValues", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValues_loop___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("list of values must not be empty", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValues_loop___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValues_loop___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValues_loop___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("case", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValues_loop___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
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
static lean_object* _init_l_Lean_Meta_caseValues_loop___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
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
x_14 = l_Lean_Meta_caseValues_loop___closed__1;
x_15 = l_Lean_Meta_caseValues_loop___closed__5;
x_16 = l_Lean_Meta_throwTacticEx___redArg(x_14, x_5, x_15, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_79; lean_object* x_80; 
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
x_79 = lean_name_append_index_after(x_29, x_4);
lean_inc(x_26);
x_80 = l_Lean_Meta_appendTagSuffix(x_26, x_79, x_9, x_10, x_11, x_12, x_24);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_105; uint8_t x_106; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_unsigned_to_nat(0u);
x_105 = lean_array_get_size(x_7);
x_106 = lean_nat_dec_lt(x_82, x_105);
if (x_106 == 0)
{
lean_dec(x_105);
lean_dec(x_23);
x_83 = x_26;
x_84 = x_81;
goto block_104;
}
else
{
uint8_t x_107; 
x_107 = lean_nat_dec_le(x_105, x_105);
if (x_107 == 0)
{
lean_dec(x_105);
lean_dec(x_23);
x_83 = x_26;
x_84 = x_81;
goto block_104;
}
else
{
size_t x_108; size_t x_109; lean_object* x_110; 
x_108 = 0;
x_109 = lean_usize_of_nat(x_105);
lean_dec(x_105);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_110 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_caseValues_loop_spec__0(x_23, x_7, x_108, x_109, x_26, x_9, x_10, x_11, x_12, x_81);
lean_dec(x_23);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_83 = x_111;
x_84 = x_112;
goto block_104;
}
else
{
uint8_t x_113; 
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
x_113 = !lean_is_exclusive(x_110);
if (x_113 == 0)
{
return x_110;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_110, 0);
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_110);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
block_104:
{
if (x_3 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = l_Lean_Meta_caseValues_loop___closed__8;
x_86 = lean_array_push(x_85, x_27);
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_28);
x_88 = lean_array_push(x_8, x_87);
x_30 = x_88;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_12;
x_35 = x_84;
goto block_78;
}
else
{
lean_object* x_89; uint8_t x_90; uint8_t x_91; lean_object* x_92; 
x_89 = lean_box(0);
x_90 = lean_unbox(x_89);
x_91 = lean_unbox(x_89);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_92 = l_Lean_Meta_substCore(x_83, x_27, x_90, x_28, x_3, x_91, x_9, x_10, x_11, x_12, x_84);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = l_Lean_Meta_caseValues_loop___closed__9;
x_98 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_98, 2, x_95);
x_99 = lean_array_push(x_8, x_98);
x_30 = x_99;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_12;
x_35 = x_94;
goto block_78;
}
else
{
uint8_t x_100; 
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
x_100 = !lean_is_exclusive(x_92);
if (x_100 == 0)
{
return x_92;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_92, 0);
x_102 = lean_ctor_get(x_92, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_92);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
else
{
uint8_t x_117; 
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
x_117 = !lean_is_exclusive(x_80);
if (x_117 == 0)
{
return x_80;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_80, 0);
x_119 = lean_ctor_get(x_80, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_80);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
block_78:
{
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_36; 
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_25, 1);
x_39 = lean_ctor_get(x_25, 2);
lean_dec(x_39);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_4, x_40);
lean_dec(x_4);
x_42 = lean_name_append_index_after(x_29, x_41);
lean_inc(x_37);
x_43 = l_Lean_Meta_appendTagSuffix(x_37, x_42, x_31, x_32, x_33, x_34, x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_array_push(x_7, x_38);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 1, x_46);
x_47 = lean_array_push(x_30, x_25);
lean_ctor_set(x_43, 0, x_47);
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_dec(x_43);
x_49 = lean_array_push(x_7, x_38);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 1, x_49);
x_50 = lean_array_push(x_30, x_25);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_free_object(x_25);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_30);
lean_dec(x_7);
x_52 = !lean_is_exclusive(x_43);
if (x_52 == 0)
{
return x_43;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_43, 0);
x_54 = lean_ctor_get(x_43, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_43);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_25, 0);
x_57 = lean_ctor_get(x_25, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_25);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_4, x_58);
lean_dec(x_4);
x_60 = lean_name_append_index_after(x_29, x_59);
lean_inc(x_56);
x_61 = l_Lean_Meta_appendTagSuffix(x_56, x_60, x_31, x_32, x_33, x_34, x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_array_push(x_7, x_57);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_20);
x_66 = lean_array_push(x_30, x_65);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_30);
lean_dec(x_7);
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
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_25, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_25, 1);
lean_inc(x_73);
lean_dec(x_25);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_add(x_4, x_74);
lean_dec(x_4);
x_76 = lean_array_push(x_7, x_73);
x_4 = x_75;
x_5 = x_72;
x_6 = x_18;
x_7 = x_76;
x_8 = x_30;
x_9 = x_31;
x_10 = x_32;
x_11 = x_33;
x_12 = x_34;
x_13 = x_35;
goto _start;
}
}
}
else
{
uint8_t x_121; 
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
x_121 = !lean_is_exclusive(x_21);
if (x_121 == 0)
{
return x_21;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_21, 0);
x_123 = lean_ctor_get(x_21, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_21);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_caseValues_loop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_caseValues_loop_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
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
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_array_to_list(x_3);
x_13 = l_Lean_Meta_caseValues_loop___closed__9;
x_14 = l_Lean_Meta_caseValues_loop(x_2, x_4, x_5, x_11, x_1, x_12, x_13, x_13, x_6, x_7, x_8, x_9, x_10);
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
l_Lean_Meta_instInhabitedCaseValueSubgoal___closed__0 = _init_l_Lean_Meta_instInhabitedCaseValueSubgoal___closed__0();
lean_mark_persistent(l_Lean_Meta_instInhabitedCaseValueSubgoal___closed__0);
l_Lean_Meta_instInhabitedCaseValueSubgoal = _init_l_Lean_Meta_instInhabitedCaseValueSubgoal();
lean_mark_persistent(l_Lean_Meta_instInhabitedCaseValueSubgoal);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__0 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__0);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__1 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__1);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__2 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__2);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__3 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__3);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__4 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__4);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__5 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__5);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__6 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__6);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__7 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__0___closed__7);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__0 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__0);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__1 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__1);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__2 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__2);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__3 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__3);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__4 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__4);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__5 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__5);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__6 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__6);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__7 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__7);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__8 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__8);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__9 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__9);
l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__10 = _init_l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseValues_0__Lean_Meta_caseValueAux___lam__1___closed__10);
l_Lean_Meta_caseValue___closed__0 = _init_l_Lean_Meta_caseValue___closed__0();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__0);
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
l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__0 = _init_l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__0();
lean_mark_persistent(l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__0);
l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__1 = _init_l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedCaseValuesSubgoal___closed__1);
l_Lean_Meta_instInhabitedCaseValuesSubgoal = _init_l_Lean_Meta_instInhabitedCaseValuesSubgoal();
lean_mark_persistent(l_Lean_Meta_instInhabitedCaseValuesSubgoal);
l_Lean_Meta_caseValues_loop___closed__0 = _init_l_Lean_Meta_caseValues_loop___closed__0();
lean_mark_persistent(l_Lean_Meta_caseValues_loop___closed__0);
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
l_Lean_Meta_caseValues_loop___closed__9 = _init_l_Lean_Meta_caseValues_loop___closed__9();
lean_mark_persistent(l_Lean_Meta_caseValues_loop___closed__9);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
