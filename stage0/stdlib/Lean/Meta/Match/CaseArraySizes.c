// Lean compiler output
// Module: Lean.Meta.Match.CaseArraySizes
// Imports: Lean.Meta.Tactic.Assert Lean.Meta.Match.CaseValues
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
lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_caseArraySizes_spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__6;
lean_object* l_Lean_Meta_mkLt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_caseArraySizes_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assertExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_Meta_instInhabitedCaseArraySizesSubgoal___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__4;
static lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0;
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValues(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__0;
static lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedCaseArraySizesSubgoal;
static lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__0;
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getArrayArgType___closed__3;
static lean_object* l_Lean_Meta_getArrayArgType___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getArrayArgType___closed__2;
static lean_object* l_Lean_Meta_getArrayArgType___closed__1;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getArrayArgType___closed__4;
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseArraySizes___closed__0;
static lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__4;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_caseArraySizes_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_caseArraySizes_spec__0(size_t, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Meta_getArrayArgType___closed__5;
static lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__1;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedCaseArraySizesSubgoal___closed__1;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_caseArraySizes___closed__2;
static lean_object* l_Lean_Meta_caseArraySizes___closed__1;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_instInhabitedCaseArraySizesSubgoal___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCaseArraySizesSubgoal___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_instInhabitedCaseArraySizesSubgoal___closed__0;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedCaseArraySizesSubgoal() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedCaseArraySizesSubgoal___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getArrayArgType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Array", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getArrayArgType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getArrayArgType___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getArrayArgType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("array expected", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getArrayArgType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getArrayArgType___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getArrayArgType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getArrayArgType___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getArrayArgType___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayArgType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Meta_whnfD(x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Meta_getArrayArgType___closed__1;
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Expr_isAppOfArity(x_13, x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_free_object(x_11);
lean_dec(x_13);
x_18 = l_Lean_Meta_getArrayArgType___closed__3;
x_19 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_7, 7);
lean_ctor_set(x_7, 1, x_19);
lean_ctor_set(x_7, 0, x_18);
x_20 = l_Lean_Meta_getArrayArgType___closed__5;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_21, x_2, x_3, x_4, x_5, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_free_object(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = l_Lean_Expr_appArg_x21(x_13);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_27);
return x_11;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = l_Lean_Meta_getArrayArgType___closed__1;
x_31 = lean_unsigned_to_nat(1u);
x_32 = l_Lean_Expr_isAppOfArity(x_28, x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_28);
x_33 = l_Lean_Meta_getArrayArgType___closed__3;
x_34 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_7, 7);
lean_ctor_set(x_7, 1, x_34);
lean_ctor_set(x_7, 0, x_33);
x_35 = l_Lean_Meta_getArrayArgType___closed__5;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_7);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_36, x_2, x_3, x_4, x_5, x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_free_object(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = l_Lean_Expr_appArg_x21(x_28);
lean_dec(x_28);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_29);
return x_43;
}
}
}
else
{
lean_free_object(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_7, 0);
x_45 = lean_ctor_get(x_7, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_46 = l_Lean_Meta_whnfD(x_44, x_2, x_3, x_4, x_5, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
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
x_50 = l_Lean_Meta_getArrayArgType___closed__1;
x_51 = lean_unsigned_to_nat(1u);
x_52 = l_Lean_Expr_isAppOfArity(x_47, x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_49);
lean_dec(x_47);
x_53 = l_Lean_Meta_getArrayArgType___closed__3;
x_54 = l_Lean_indentExpr(x_1);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Meta_getArrayArgType___closed__5;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_57, x_2, x_3, x_4, x_5, x_48);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
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
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = l_Lean_Expr_appArg_x21(x_47);
lean_dec(x_47);
if (lean_is_scalar(x_49)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_49;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_48);
return x_64;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_46;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("getLit", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__0;
x_2 = l_Lean_Meta_getArrayArgType___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_mkRawNatLit(x_2);
x_11 = l_Lean_mkRawNatLit(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_10);
x_12 = l_Lean_Meta_mkLt(x_10, x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Meta_mkDecideProof(x_13, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1;
x_19 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__2;
x_20 = lean_array_push(x_19, x_1);
x_21 = lean_array_push(x_20, x_10);
x_22 = lean_array_push(x_21, x_4);
x_23 = lean_array_push(x_22, x_16);
x_24 = l_Lean_Meta_mkAppM(x_18, x_23, x_5, x_6, x_7, x_8, x_17);
return x_24;
}
else
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_getType(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_push(x_2, x_6);
x_16 = lean_box(1);
x_17 = lean_box(1);
x_18 = lean_unbox(x_16);
x_19 = lean_unbox(x_17);
x_20 = l_Lean_Meta_mkForallFVars(x_15, x_13, x_3, x_18, x_19, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_array_push(x_4, x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_array_push(x_4, x_5);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_17 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(x_1, x_2, x_3, x_4, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_push(x_5, x_11);
x_21 = lean_array_push(x_6, x_18);
x_22 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(x_7, x_1, x_3, x_8, x_4, x_9, x_10, x_20, x_21, x_12, x_13, x_14, x_15, x_19);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_15);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toArrayLit_eq", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__0;
x_2 = l_Lean_Meta_getArrayArgType___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hEqALit", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_7, x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_4);
lean_inc(x_8);
x_16 = lean_array_to_list(x_8);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_17 = l_Lean_Meta_mkArrayLit(x_6, x_16, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_20 = l_Lean_Meta_mkEq(x_2, x_18, x_10, x_11, x_12, x_13, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1;
x_24 = l_Lean_mkRawNatLit(x_3);
x_25 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2;
x_26 = lean_array_push(x_25, x_2);
x_27 = lean_array_push(x_26, x_24);
x_28 = lean_array_push(x_27, x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_29 = l_Lean_Meta_mkAppM(x_23, x_28, x_10, x_11, x_12, x_13, x_22);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_box(x_15);
x_33 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0___boxed), 11, 5);
lean_closure_set(x_33, 0, x_1);
lean_closure_set(x_33, 1, x_8);
lean_closure_set(x_33, 2, x_32);
lean_closure_set(x_33, 3, x_9);
lean_closure_set(x_33, 4, x_30);
x_34 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__4;
x_35 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2___redArg(x_34, x_21, x_33, x_10, x_11, x_12, x_13, x_31);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_17);
if (x_44 == 0)
{
return x_17;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_17, 0);
x_46 = lean_ctor_get(x_17, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_17);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_7, x_48);
lean_inc(x_49);
lean_inc(x_6);
lean_inc(x_4);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1), 16, 10);
lean_closure_set(x_50, 0, x_2);
lean_closure_set(x_50, 1, x_7);
lean_closure_set(x_50, 2, x_3);
lean_closure_set(x_50, 3, x_5);
lean_closure_set(x_50, 4, x_8);
lean_closure_set(x_50, 5, x_9);
lean_closure_set(x_50, 6, x_1);
lean_closure_set(x_50, 7, x_4);
lean_closure_set(x_50, 8, x_6);
lean_closure_set(x_50, 9, x_49);
x_51 = lean_name_append_index_after(x_4, x_49);
x_52 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__2___redArg(x_51, x_6, x_50, x_10, x_11, x_12, x_13, x_14);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_11 = l_Lean_Meta_getArrayArgType(x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(x_1, x_2, x_3, x_4, x_5, x_12, x_14, x_15, x_15, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
lean_inc(x_1);
x_21 = l_Lean_MVarId_getTag(x_1, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_19, x_22, x_6, x_7, x_8, x_9, x_23);
lean_dec(x_9);
lean_dec(x_8);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_25);
x_27 = l_Lean_mkAppN(x_25, x_20);
lean_dec(x_20);
x_28 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_27, x_7, x_26);
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = l_Lean_Expr_mvarId_x21(x_25);
lean_dec(x_25);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = l_Lean_Expr_mvarId_x21(x_25);
lean_dec(x_25);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
return x_16;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_16, 0);
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_16);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_11);
if (x_43 == 0)
{
return x_11;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_caseArraySizes_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_mkRawNatLit(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_caseArraySizes_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Lean_Meta_FVarSubst_get(x_1, x_6);
x_10 = l_Lean_Expr_fvarId_x21(x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_10);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_17 = l_Lean_Meta_mkEqSymm(x_1, x_12, x_13, x_14, x_15, x_16);
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
lean_inc(x_4);
x_20 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(x_2, x_3, x_4, x_5, x_18, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_24 = l_Lean_Meta_introNCore(x_21, x_4, x_23, x_6, x_7, x_12, x_13, x_14, x_15, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_29 = l_Lean_Meta_intro1Core(x_28, x_7, x_12, x_13, x_14, x_15, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_34 = l_Lean_MVarId_clear(x_33, x_8, x_12, x_13, x_14, x_15, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Meta_substCore(x_35, x_32, x_6, x_9, x_10, x_6, x_12, x_13, x_14, x_15, x_36);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_mk_empty_array_with_capacity(x_11);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_27);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set(x_43, 3, x_40);
lean_ctor_set(x_37, 0, x_43);
return x_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_37, 0);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_37);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_mk_empty_array_with_capacity(x_11);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_27);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_27);
x_51 = !lean_is_exclusive(x_37);
if (x_51 == 0)
{
return x_37;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_37, 0);
x_53 = lean_ctor_get(x_37, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_37);
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
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
x_55 = !lean_is_exclusive(x_34);
if (x_55 == 0)
{
return x_34;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_34, 0);
x_57 = lean_ctor_get(x_34, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_34);
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
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_59 = !lean_is_exclusive(x_29);
if (x_59 == 0)
{
return x_29;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_29, 0);
x_61 = lean_ctor_get(x_29, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_29);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_63 = !lean_is_exclusive(x_24);
if (x_63 == 0)
{
return x_24;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_24, 0);
x_65 = lean_ctor_get(x_24, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_24);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_20);
if (x_67 == 0)
{
return x_20;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_20, 0);
x_69 = lean_ctor_get(x_20, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_20);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_17);
if (x_71 == 0)
{
return x_17;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_17, 0);
x_73 = lean_ctor_get(x_17, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_17);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_8, x_16);
if (x_17 == 1)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_31; uint8_t x_32; 
x_19 = lean_array_fget(x_7, x_9);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 2);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_8, x_23);
lean_dec(x_8);
x_31 = lean_array_get_size(x_1);
x_32 = lean_nat_dec_lt(x_9, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_box(1);
x_34 = lean_unbox(x_33);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_2);
x_35 = l_Lean_Meta_substCore(x_20, x_2, x_3, x_22, x_34, x_3, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_array_size(x_21);
x_41 = 0;
x_42 = l_Array_mapMUnsafe_map___at___Lean_Meta_caseArraySizes_spec__1(x_38, x_40, x_41, x_21);
x_43 = l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg___closed__0;
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_42);
lean_ctor_set(x_44, 3, x_38);
x_25 = x_44;
x_26 = x_37;
goto block_30;
}
else
{
uint8_t x_45; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_35);
if (x_45 == 0)
{
return x_35;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_35, 0);
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_35);
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
x_49 = lean_box(0);
x_50 = lean_array_get(x_49, x_21, x_16);
lean_dec(x_21);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_51 = l_Lean_MVarId_clear(x_20, x_50, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_4);
x_54 = l_Lean_Meta_FVarSubst_get(x_22, x_4);
x_55 = l_Lean_Expr_fvarId_x21(x_54);
lean_dec(x_54);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_56 = l_Lean_MVarId_clear(x_52, x_55, x_11, x_12, x_13, x_14, x_53);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_2);
x_59 = l_Lean_Meta_FVarSubst_get(x_22, x_2);
x_60 = l_Lean_Expr_fvarId_x21(x_59);
lean_dec(x_59);
x_61 = lean_array_fget(x_1, x_9);
lean_inc(x_60);
x_62 = l_Lean_Expr_fvar___override(x_60);
x_63 = lean_box(x_3);
x_64 = lean_box(x_17);
x_65 = lean_box(x_32);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_57);
x_66 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg___lam__0___boxed), 16, 11);
lean_closure_set(x_66, 0, x_62);
lean_closure_set(x_66, 1, x_57);
lean_closure_set(x_66, 2, x_5);
lean_closure_set(x_66, 3, x_61);
lean_closure_set(x_66, 4, x_6);
lean_closure_set(x_66, 5, x_63);
lean_closure_set(x_66, 6, x_64);
lean_closure_set(x_66, 7, x_60);
lean_closure_set(x_66, 8, x_22);
lean_closure_set(x_66, 9, x_65);
lean_closure_set(x_66, 10, x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_67 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_57, x_66, x_11, x_12, x_13, x_14, x_58);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_25 = x_68;
x_26 = x_69;
goto block_30;
}
else
{
uint8_t x_70; 
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_67, 0);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_67);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_56);
if (x_74 == 0)
{
return x_56;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_56, 0);
x_76 = lean_ctor_get(x_56, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_56);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_51);
if (x_78 == 0)
{
return x_51;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_51, 0);
x_80 = lean_ctor_get(x_51, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_51);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
block_30:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_28 = lean_array_push(x_10, x_25);
x_8 = x_24;
x_9 = x_27;
x_10 = x_28;
x_15 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_8, x_16);
if (x_17 == 1)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_31; uint8_t x_32; 
x_19 = lean_array_fget(x_7, x_9);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 2);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_8, x_23);
x_31 = lean_array_get_size(x_1);
x_32 = lean_nat_dec_lt(x_9, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_box(1);
x_34 = lean_unbox(x_33);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_2);
x_35 = l_Lean_Meta_substCore(x_20, x_2, x_3, x_22, x_34, x_3, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_array_size(x_21);
x_41 = 0;
x_42 = l_Array_mapMUnsafe_map___at___Lean_Meta_caseArraySizes_spec__1(x_38, x_40, x_41, x_21);
x_43 = l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg___closed__0;
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_42);
lean_ctor_set(x_44, 3, x_38);
x_25 = x_44;
x_26 = x_37;
goto block_30;
}
else
{
uint8_t x_45; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_35);
if (x_45 == 0)
{
return x_35;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_35, 0);
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_35);
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
x_49 = lean_box(0);
x_50 = lean_array_get(x_49, x_21, x_16);
lean_dec(x_21);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_51 = l_Lean_MVarId_clear(x_20, x_50, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_4);
x_54 = l_Lean_Meta_FVarSubst_get(x_22, x_4);
x_55 = l_Lean_Expr_fvarId_x21(x_54);
lean_dec(x_54);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_56 = l_Lean_MVarId_clear(x_52, x_55, x_11, x_12, x_13, x_14, x_53);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_2);
x_59 = l_Lean_Meta_FVarSubst_get(x_22, x_2);
x_60 = l_Lean_Expr_fvarId_x21(x_59);
lean_dec(x_59);
x_61 = lean_array_fget(x_1, x_9);
lean_inc(x_60);
x_62 = l_Lean_Expr_fvar___override(x_60);
x_63 = lean_box(x_3);
x_64 = lean_box(x_17);
x_65 = lean_box(x_32);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_57);
x_66 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg___lam__0___boxed), 16, 11);
lean_closure_set(x_66, 0, x_62);
lean_closure_set(x_66, 1, x_57);
lean_closure_set(x_66, 2, x_5);
lean_closure_set(x_66, 3, x_61);
lean_closure_set(x_66, 4, x_6);
lean_closure_set(x_66, 5, x_63);
lean_closure_set(x_66, 6, x_64);
lean_closure_set(x_66, 7, x_60);
lean_closure_set(x_66, 8, x_22);
lean_closure_set(x_66, 9, x_65);
lean_closure_set(x_66, 10, x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_67 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_57, x_66, x_11, x_12, x_13, x_14, x_58);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_25 = x_68;
x_26 = x_69;
goto block_30;
}
else
{
uint8_t x_70; 
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_67, 0);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_67);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_56);
if (x_74 == 0)
{
return x_56;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_56, 0);
x_76 = lean_ctor_get(x_56, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_56);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_51);
if (x_78 == 0)
{
return x_51;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_51, 0);
x_80 = lean_ctor_get(x_51, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_51);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
block_30:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_nat_add(x_9, x_23);
x_28 = lean_array_push(x_10, x_25);
x_29 = l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_24, x_27, x_28, x_11, x_12, x_13, x_14, x_26);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Meta_caseArraySizes___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("aSize", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseArraySizes___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseArraySizes___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseArraySizes___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseArraySizes___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseArraySizes___lam__0___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_caseArraySizes___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseArraySizes___lam__0___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_caseArraySizes___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseArraySizes___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseArraySizes___lam__0___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = l_Lean_Meta_mkAppM(x_1, x_2, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_caseArraySizes___lam__0___closed__1;
x_17 = l_Lean_Meta_caseArraySizes___lam__0___closed__4;
x_18 = l_Lean_Meta_caseArraySizes___lam__0___closed__6;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_MVarId_assertExt(x_3, x_16, x_17, x_14, x_18, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_24 = l_Lean_Meta_intro1Core(x_20, x_23, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_unbox(x_22);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_30 = l_Lean_Meta_intro1Core(x_28, x_29, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_array_size(x_4);
x_36 = 0;
lean_inc(x_4);
x_37 = l_Array_mapMUnsafe_map___at___Lean_Meta_caseArraySizes_spec__0(x_35, x_36, x_4);
x_38 = lean_unbox(x_22);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_27);
x_39 = l_Lean_Meta_caseValues(x_34, x_27, x_37, x_5, x_38, x_8, x_9, x_10, x_11, x_32);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_array_get_size(x_40);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_mk_empty_array_with_capacity(x_42);
x_45 = lean_unbox(x_22);
x_46 = l_Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2___redArg(x_4, x_33, x_45, x_27, x_6, x_7, x_40, x_42, x_43, x_44, x_8, x_9, x_10, x_11, x_41);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_4);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_39);
if (x_47 == 0)
{
return x_39;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_39, 0);
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_39);
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
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_30);
if (x_51 == 0)
{
return x_30;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_30, 0);
x_53 = lean_ctor_get(x_30, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_30);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_24);
if (x_55 == 0)
{
return x_24;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_24, 0);
x_57 = lean_ctor_get(x_24, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_24);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_19);
if (x_59 == 0)
{
return x_19;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_19, 0);
x_61 = lean_ctor_get(x_19, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_19);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_13);
if (x_63 == 0)
{
return x_13;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_13, 0);
x_65 = lean_ctor_get(x_13, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_13);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
static lean_object* _init_l_Lean_Meta_caseArraySizes___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("size", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseArraySizes___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_caseArraySizes___closed__0;
x_2 = l_Lean_Meta_getArrayArgType___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_caseArraySizes___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_Expr_fvar___override(x_2);
x_12 = l_Lean_Meta_caseArraySizes___closed__1;
x_13 = l_Lean_Meta_caseArraySizes___closed__2;
lean_inc(x_11);
x_14 = lean_array_push(x_13, x_11);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_caseArraySizes___lam__0), 12, 7);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_1);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_5);
lean_closure_set(x_15, 5, x_11);
lean_closure_set(x_15, 6, x_4);
x_16 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_15, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_caseArraySizes_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Meta_caseArraySizes_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_caseArraySizes_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Meta_caseArraySizes_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = lean_unbox(x_10);
lean_dec(x_10);
x_20 = l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_8, x_9, x_19, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2(x_1, x_2, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = l_Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2___redArg(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = l_Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2(x_1, x_2, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_18;
}
}
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_CaseValues(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_CaseArraySizes(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_CaseValues(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedCaseArraySizesSubgoal___closed__0 = _init_l_Lean_Meta_instInhabitedCaseArraySizesSubgoal___closed__0();
lean_mark_persistent(l_Lean_Meta_instInhabitedCaseArraySizesSubgoal___closed__0);
l_Lean_Meta_instInhabitedCaseArraySizesSubgoal___closed__1 = _init_l_Lean_Meta_instInhabitedCaseArraySizesSubgoal___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedCaseArraySizesSubgoal___closed__1);
l_Lean_Meta_instInhabitedCaseArraySizesSubgoal = _init_l_Lean_Meta_instInhabitedCaseArraySizesSubgoal();
lean_mark_persistent(l_Lean_Meta_instInhabitedCaseArraySizesSubgoal);
l_Lean_Meta_getArrayArgType___closed__0 = _init_l_Lean_Meta_getArrayArgType___closed__0();
lean_mark_persistent(l_Lean_Meta_getArrayArgType___closed__0);
l_Lean_Meta_getArrayArgType___closed__1 = _init_l_Lean_Meta_getArrayArgType___closed__1();
lean_mark_persistent(l_Lean_Meta_getArrayArgType___closed__1);
l_Lean_Meta_getArrayArgType___closed__2 = _init_l_Lean_Meta_getArrayArgType___closed__2();
lean_mark_persistent(l_Lean_Meta_getArrayArgType___closed__2);
l_Lean_Meta_getArrayArgType___closed__3 = _init_l_Lean_Meta_getArrayArgType___closed__3();
lean_mark_persistent(l_Lean_Meta_getArrayArgType___closed__3);
l_Lean_Meta_getArrayArgType___closed__4 = _init_l_Lean_Meta_getArrayArgType___closed__4();
lean_mark_persistent(l_Lean_Meta_getArrayArgType___closed__4);
l_Lean_Meta_getArrayArgType___closed__5 = _init_l_Lean_Meta_getArrayArgType___closed__5();
lean_mark_persistent(l_Lean_Meta_getArrayArgType___closed__5);
l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__0 = _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__0);
l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1 = _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1);
l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__2 = _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__2);
l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__0 = _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__0);
l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1 = _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1);
l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2 = _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2);
l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3 = _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3);
l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__4 = _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__4);
l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0 = _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0);
l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg___closed__0 = _init_l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg___closed__0();
lean_mark_persistent(l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Meta_caseArraySizes_spec__2_spec__2___redArg___closed__0);
l_Lean_Meta_caseArraySizes___lam__0___closed__0 = _init_l_Lean_Meta_caseArraySizes___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_caseArraySizes___lam__0___closed__0);
l_Lean_Meta_caseArraySizes___lam__0___closed__1 = _init_l_Lean_Meta_caseArraySizes___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_caseArraySizes___lam__0___closed__1);
l_Lean_Meta_caseArraySizes___lam__0___closed__2 = _init_l_Lean_Meta_caseArraySizes___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_caseArraySizes___lam__0___closed__2);
l_Lean_Meta_caseArraySizes___lam__0___closed__3 = _init_l_Lean_Meta_caseArraySizes___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_caseArraySizes___lam__0___closed__3);
l_Lean_Meta_caseArraySizes___lam__0___closed__4 = _init_l_Lean_Meta_caseArraySizes___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_caseArraySizes___lam__0___closed__4);
l_Lean_Meta_caseArraySizes___lam__0___closed__5 = _init_l_Lean_Meta_caseArraySizes___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_caseArraySizes___lam__0___closed__5);
l_Lean_Meta_caseArraySizes___lam__0___closed__6 = _init_l_Lean_Meta_caseArraySizes___lam__0___closed__6();
lean_mark_persistent(l_Lean_Meta_caseArraySizes___lam__0___closed__6);
l_Lean_Meta_caseArraySizes___closed__0 = _init_l_Lean_Meta_caseArraySizes___closed__0();
lean_mark_persistent(l_Lean_Meta_caseArraySizes___closed__0);
l_Lean_Meta_caseArraySizes___closed__1 = _init_l_Lean_Meta_caseArraySizes___closed__1();
lean_mark_persistent(l_Lean_Meta_caseArraySizes___closed__1);
l_Lean_Meta_caseArraySizes___closed__2 = _init_l_Lean_Meta_caseArraySizes___closed__2();
lean_mark_persistent(l_Lean_Meta_caseArraySizes___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
