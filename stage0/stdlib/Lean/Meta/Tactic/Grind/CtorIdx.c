// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.CtorIdx
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Constructions.CtorIdx import Lean.Meta.CtorIdxHInj
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
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(lean_object*);
lean_object* l_Lean_executeReservedNameAction(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4;
lean_object* lean_st_ref_get(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2;
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3;
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_isCtorIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0;
x_13 = lean_panic_fn(x_12, x_1);
x_14 = lean_apply_10(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_14;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.CtorIdx", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.propagateCtorIdxUp", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: aType.isAppOfArity indInfo.name (indInfo.numParams + indInfo.numIndices)\n      -- both types should be headed by the same type former\n      ", 161, 161);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_unsigned_to_nat(37u);
x_4 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2;
x_5 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_17);
lean_dec_ref(x_3);
x_18 = lean_array_set(x_4, x_5, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_5, x_19);
lean_dec(x_5);
x_3 = x_16;
x_4 = x_18;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_5);
x_22 = l_Lean_Expr_constName_x3f(x_3);
lean_dec_ref(x_3);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = l_isCtorIdx_x3f___redArg(x_23, x_14);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 2);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_array_get_size(x_4);
x_34 = lean_nat_add(x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_34, x_35);
x_37 = lean_nat_dec_eq(x_33, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_38 = lean_box(0);
lean_ctor_set(x_25, 0, x_38);
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_free_object(x_25);
x_39 = l_Array_back_x21___redArg(x_1, x_4);
lean_dec_ref(x_4);
lean_inc(x_39);
x_40 = l_Lean_Meta_Grind_getRootENode___redArg(x_39, x_6, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_42, 0);
lean_inc_ref(x_43);
x_44 = lean_ctor_get_uint8(x_42, sizeof(void*)*11 + 2);
x_45 = lean_ctor_get_uint8(x_42, sizeof(void*)*11 + 4);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_89; 
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_89 = lean_box(0);
lean_ctor_set(x_40, 0, x_89);
return x_40;
}
else
{
lean_object* x_90; 
lean_free_object(x_40);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_43);
x_90 = l_Lean_Meta_isConstructorApp_x3f(x_43, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_90, 0);
if (lean_obj_tag(x_92) == 1)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_free_object(x_90);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
if (x_45 == 0)
{
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
x_94 = x_6;
x_95 = x_7;
x_96 = x_8;
x_97 = x_9;
x_98 = x_10;
x_99 = x_11;
x_100 = x_12;
x_101 = x_13;
x_102 = x_14;
x_103 = lean_box(0);
goto block_133;
}
else
{
lean_object* x_134; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_43);
lean_inc(x_39);
x_134 = l_Lean_Meta_Grind_hasSameType(x_39, x_43, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
x_136 = lean_unbox(x_135);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
lean_dec(x_93);
lean_dec_ref(x_2);
x_137 = l_Lean_Meta_Grind_getGeneration___redArg(x_39, x_6);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
x_139 = l_Lean_Meta_Grind_getGeneration___redArg(x_43, x_6);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_192; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
x_192 = lean_nat_dec_le(x_138, x_140);
if (x_192 == 0)
{
lean_dec(x_140);
x_141 = x_138;
goto block_191;
}
else
{
lean_dec(x_138);
x_141 = x_140;
goto block_191;
}
block_191:
{
lean_object* x_142; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_39);
x_142 = lean_infer_type(x_39, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_144 = l_Lean_Meta_whnfD(x_143, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_43);
x_146 = lean_infer_type(x_43, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec_ref(x_146);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_148 = l_Lean_Meta_whnfD(x_147, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_148) == 0)
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_150 = lean_ctor_get(x_148, 0);
x_151 = lean_ctor_get(x_30, 0);
lean_inc(x_151);
lean_dec_ref(x_30);
lean_inc(x_34);
x_152 = l_Lean_Expr_isAppOfArity(x_145, x_151, x_34);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_151);
lean_free_object(x_148);
lean_dec(x_150);
lean_dec(x_145);
lean_dec(x_141);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_24);
x_153 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4;
x_154 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_153, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_154;
}
else
{
uint8_t x_155; 
x_155 = l_Lean_Expr_isAppOfArity(x_150, x_151, x_34);
if (x_155 == 0)
{
lean_object* x_156; 
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_145);
lean_dec(x_141);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_156 = lean_box(0);
lean_ctor_set(x_148, 0, x_156);
return x_148;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_free_object(x_148);
x_157 = lean_st_ref_get(x_14);
x_158 = lean_ctor_get(x_157, 0);
lean_inc_ref(x_158);
lean_dec(x_157);
x_159 = l_Lean_Expr_getAppFn(x_145);
x_160 = l_Lean_Expr_constLevels_x21(x_159);
lean_dec_ref(x_159);
x_161 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_151);
x_162 = l_Lean_Environment_containsOnBranch(x_158, x_161);
if (x_162 == 0)
{
lean_object* x_163; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_161);
x_163 = l_Lean_executeReservedNameAction(x_161, x_13, x_14);
if (lean_obj_tag(x_163) == 0)
{
lean_dec_ref(x_163);
x_46 = x_141;
x_47 = x_161;
x_48 = x_145;
x_49 = x_160;
x_50 = x_150;
x_51 = x_6;
x_52 = x_7;
x_53 = x_8;
x_54 = x_9;
x_55 = x_10;
x_56 = x_11;
x_57 = x_12;
x_58 = x_13;
x_59 = x_14;
x_60 = lean_box(0);
goto block_88;
}
else
{
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_150);
lean_dec(x_145);
lean_dec(x_141);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_163;
}
}
else
{
x_46 = x_141;
x_47 = x_161;
x_48 = x_145;
x_49 = x_160;
x_50 = x_150;
x_51 = x_6;
x_52 = x_7;
x_53 = x_8;
x_54 = x_9;
x_55 = x_10;
x_56 = x_11;
x_57 = x_12;
x_58 = x_13;
x_59 = x_14;
x_60 = lean_box(0);
goto block_88;
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get(x_148, 0);
lean_inc(x_164);
lean_dec(x_148);
x_165 = lean_ctor_get(x_30, 0);
lean_inc(x_165);
lean_dec_ref(x_30);
lean_inc(x_34);
x_166 = l_Lean_Expr_isAppOfArity(x_145, x_165, x_34);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_145);
lean_dec(x_141);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_24);
x_167 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4;
x_168 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_167, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_168;
}
else
{
uint8_t x_169; 
x_169 = l_Lean_Expr_isAppOfArity(x_164, x_165, x_34);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_145);
lean_dec(x_141);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_170 = lean_box(0);
x_171 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_171, 0, x_170);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_172 = lean_st_ref_get(x_14);
x_173 = lean_ctor_get(x_172, 0);
lean_inc_ref(x_173);
lean_dec(x_172);
x_174 = l_Lean_Expr_getAppFn(x_145);
x_175 = l_Lean_Expr_constLevels_x21(x_174);
lean_dec_ref(x_174);
x_176 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_165);
x_177 = l_Lean_Environment_containsOnBranch(x_173, x_176);
if (x_177 == 0)
{
lean_object* x_178; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_176);
x_178 = l_Lean_executeReservedNameAction(x_176, x_13, x_14);
if (lean_obj_tag(x_178) == 0)
{
lean_dec_ref(x_178);
x_46 = x_141;
x_47 = x_176;
x_48 = x_145;
x_49 = x_175;
x_50 = x_164;
x_51 = x_6;
x_52 = x_7;
x_53 = x_8;
x_54 = x_9;
x_55 = x_10;
x_56 = x_11;
x_57 = x_12;
x_58 = x_13;
x_59 = x_14;
x_60 = lean_box(0);
goto block_88;
}
else
{
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_164);
lean_dec(x_145);
lean_dec(x_141);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_178;
}
}
else
{
x_46 = x_141;
x_47 = x_176;
x_48 = x_145;
x_49 = x_175;
x_50 = x_164;
x_51 = x_6;
x_52 = x_7;
x_53 = x_8;
x_54 = x_9;
x_55 = x_10;
x_56 = x_11;
x_57 = x_12;
x_58 = x_13;
x_59 = x_14;
x_60 = lean_box(0);
goto block_88;
}
}
}
}
}
else
{
uint8_t x_179; 
lean_dec(x_145);
lean_dec(x_141);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_179 = !lean_is_exclusive(x_148);
if (x_179 == 0)
{
return x_148;
}
else
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_148, 0);
lean_inc(x_180);
lean_dec(x_148);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_180);
return x_181;
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_145);
lean_dec(x_141);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_182 = !lean_is_exclusive(x_146);
if (x_182 == 0)
{
return x_146;
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_146, 0);
lean_inc(x_183);
lean_dec(x_146);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_141);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_185 = !lean_is_exclusive(x_144);
if (x_185 == 0)
{
return x_144;
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_144, 0);
lean_inc(x_186);
lean_dec(x_144);
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_141);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_188 = !lean_is_exclusive(x_142);
if (x_188 == 0)
{
return x_142;
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_142, 0);
lean_inc(x_189);
lean_dec(x_142);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_189);
return x_190;
}
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_138);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_193 = !lean_is_exclusive(x_139);
if (x_193 == 0)
{
return x_139;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_139, 0);
lean_inc(x_194);
lean_dec(x_139);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_194);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_196 = !lean_is_exclusive(x_137);
if (x_196 == 0)
{
return x_137;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_137, 0);
lean_inc(x_197);
lean_dec(x_137);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_197);
return x_198;
}
}
}
else
{
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
x_94 = x_6;
x_95 = x_7;
x_96 = x_8;
x_97 = x_9;
x_98 = x_10;
x_99 = x_11;
x_100 = x_12;
x_101 = x_13;
x_102 = x_14;
x_103 = lean_box(0);
goto block_133;
}
}
else
{
uint8_t x_199; 
lean_dec(x_93);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_199 = !lean_is_exclusive(x_134);
if (x_199 == 0)
{
return x_134;
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_134, 0);
lean_inc(x_200);
lean_dec(x_134);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
}
}
block_133:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_93, 2);
lean_inc(x_104);
lean_dec(x_93);
x_105 = l_Lean_mkNatLit(x_104);
x_106 = l_Lean_Meta_Sym_shareCommon___redArg(x_105, x_98);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
x_108 = lean_unsigned_to_nat(0u);
x_109 = lean_box(0);
lean_inc(x_102);
lean_inc_ref(x_101);
lean_inc(x_100);
lean_inc_ref(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc_ref(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_107);
x_110 = lean_grind_internalize(x_107, x_108, x_109, x_94, x_95, x_96, x_97, x_98, x_99, x_100, x_101, x_102);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; 
lean_dec_ref(x_110);
lean_inc(x_102);
lean_inc_ref(x_101);
lean_inc(x_100);
lean_inc_ref(x_99);
lean_inc_ref(x_96);
lean_inc(x_94);
x_111 = lean_grind_mk_eq_proof(x_39, x_43, x_94, x_95, x_96, x_97, x_98, x_99, x_100, x_101, x_102);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = l_Lean_Expr_appFn_x21(x_2);
lean_inc(x_102);
lean_inc_ref(x_101);
lean_inc(x_100);
lean_inc_ref(x_99);
x_114 = l_Lean_Meta_mkCongrArg(x_113, x_112, x_99, x_100, x_101, x_102);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec_ref(x_114);
lean_inc(x_102);
lean_inc_ref(x_101);
lean_inc(x_100);
lean_inc_ref(x_99);
lean_inc(x_107);
lean_inc_ref(x_2);
x_116 = l_Lean_Meta_mkEq(x_2, x_107, x_99, x_100, x_101, x_102);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
x_118 = l_Lean_Meta_mkExpectedPropHint(x_115, x_117);
x_119 = 0;
x_120 = l_Lean_Meta_Grind_pushEqCore___redArg(x_2, x_107, x_118, x_119, x_94, x_96, x_99, x_100, x_101, x_102);
lean_dec_ref(x_96);
lean_dec(x_94);
return x_120;
}
else
{
uint8_t x_121; 
lean_dec(x_115);
lean_dec(x_107);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec_ref(x_96);
lean_dec(x_94);
lean_dec_ref(x_2);
x_121 = !lean_is_exclusive(x_116);
if (x_121 == 0)
{
return x_116;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_116, 0);
lean_inc(x_122);
lean_dec(x_116);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_107);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec_ref(x_96);
lean_dec(x_94);
lean_dec_ref(x_2);
x_124 = !lean_is_exclusive(x_114);
if (x_124 == 0)
{
return x_114;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_114, 0);
lean_inc(x_125);
lean_dec(x_114);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_107);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec_ref(x_96);
lean_dec(x_94);
lean_dec_ref(x_2);
x_127 = !lean_is_exclusive(x_111);
if (x_127 == 0)
{
return x_111;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_111, 0);
lean_inc(x_128);
lean_dec(x_111);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
else
{
lean_dec(x_107);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec_ref(x_2);
return x_110;
}
}
else
{
uint8_t x_130; 
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec_ref(x_2);
x_130 = !lean_is_exclusive(x_106);
if (x_130 == 0)
{
return x_106;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_106, 0);
lean_inc(x_131);
lean_dec(x_106);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
}
}
else
{
lean_object* x_202; 
lean_dec(x_92);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_202 = lean_box(0);
lean_ctor_set(x_90, 0, x_202);
return x_90;
}
}
else
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_90, 0);
lean_inc(x_203);
lean_dec(x_90);
if (lean_obj_tag(x_203) == 1)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec_ref(x_203);
if (x_45 == 0)
{
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
x_205 = x_6;
x_206 = x_7;
x_207 = x_8;
x_208 = x_9;
x_209 = x_10;
x_210 = x_11;
x_211 = x_12;
x_212 = x_13;
x_213 = x_14;
x_214 = lean_box(0);
goto block_244;
}
else
{
lean_object* x_245; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_43);
lean_inc(x_39);
x_245 = l_Lean_Meta_Grind_hasSameType(x_39, x_43, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; uint8_t x_247; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec_ref(x_245);
x_247 = lean_unbox(x_246);
lean_dec(x_246);
if (x_247 == 0)
{
lean_object* x_248; 
lean_dec(x_204);
lean_dec_ref(x_2);
x_248 = l_Lean_Meta_Grind_getGeneration___redArg(x_39, x_6);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
lean_dec_ref(x_248);
x_250 = l_Lean_Meta_Grind_getGeneration___redArg(x_43, x_6);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_289; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
lean_dec_ref(x_250);
x_289 = lean_nat_dec_le(x_249, x_251);
if (x_289 == 0)
{
lean_dec(x_251);
x_252 = x_249;
goto block_288;
}
else
{
lean_dec(x_249);
x_252 = x_251;
goto block_288;
}
block_288:
{
lean_object* x_253; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_39);
x_253 = lean_infer_type(x_39, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_255 = l_Lean_Meta_whnfD(x_254, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
lean_dec_ref(x_255);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_43);
x_257 = lean_infer_type(x_43, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
lean_dec_ref(x_257);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_259 = l_Lean_Meta_whnfD(x_258, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 x_261 = x_259;
} else {
 lean_dec_ref(x_259);
 x_261 = lean_box(0);
}
x_262 = lean_ctor_get(x_30, 0);
lean_inc(x_262);
lean_dec_ref(x_30);
lean_inc(x_34);
x_263 = l_Lean_Expr_isAppOfArity(x_256, x_262, x_34);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; 
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_256);
lean_dec(x_252);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_24);
x_264 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4;
x_265 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_264, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_265;
}
else
{
uint8_t x_266; 
x_266 = l_Lean_Expr_isAppOfArity(x_260, x_262, x_34);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_262);
lean_dec(x_260);
lean_dec(x_256);
lean_dec(x_252);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_267 = lean_box(0);
if (lean_is_scalar(x_261)) {
 x_268 = lean_alloc_ctor(0, 1, 0);
} else {
 x_268 = x_261;
}
lean_ctor_set(x_268, 0, x_267);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
lean_dec(x_261);
x_269 = lean_st_ref_get(x_14);
x_270 = lean_ctor_get(x_269, 0);
lean_inc_ref(x_270);
lean_dec(x_269);
x_271 = l_Lean_Expr_getAppFn(x_256);
x_272 = l_Lean_Expr_constLevels_x21(x_271);
lean_dec_ref(x_271);
x_273 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_262);
x_274 = l_Lean_Environment_containsOnBranch(x_270, x_273);
if (x_274 == 0)
{
lean_object* x_275; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_273);
x_275 = l_Lean_executeReservedNameAction(x_273, x_13, x_14);
if (lean_obj_tag(x_275) == 0)
{
lean_dec_ref(x_275);
x_46 = x_252;
x_47 = x_273;
x_48 = x_256;
x_49 = x_272;
x_50 = x_260;
x_51 = x_6;
x_52 = x_7;
x_53 = x_8;
x_54 = x_9;
x_55 = x_10;
x_56 = x_11;
x_57 = x_12;
x_58 = x_13;
x_59 = x_14;
x_60 = lean_box(0);
goto block_88;
}
else
{
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_260);
lean_dec(x_256);
lean_dec(x_252);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_275;
}
}
else
{
x_46 = x_252;
x_47 = x_273;
x_48 = x_256;
x_49 = x_272;
x_50 = x_260;
x_51 = x_6;
x_52 = x_7;
x_53 = x_8;
x_54 = x_9;
x_55 = x_10;
x_56 = x_11;
x_57 = x_12;
x_58 = x_13;
x_59 = x_14;
x_60 = lean_box(0);
goto block_88;
}
}
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_256);
lean_dec(x_252);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_276 = lean_ctor_get(x_259, 0);
lean_inc(x_276);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 x_277 = x_259;
} else {
 lean_dec_ref(x_259);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 1, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_276);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_256);
lean_dec(x_252);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_279 = lean_ctor_get(x_257, 0);
lean_inc(x_279);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_280 = x_257;
} else {
 lean_dec_ref(x_257);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 1, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_279);
return x_281;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_252);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_282 = lean_ctor_get(x_255, 0);
lean_inc(x_282);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 x_283 = x_255;
} else {
 lean_dec_ref(x_255);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 1, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_282);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_252);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_285 = lean_ctor_get(x_253, 0);
lean_inc(x_285);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_286 = x_253;
} else {
 lean_dec_ref(x_253);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(1, 1, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_285);
return x_287;
}
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_249);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_290 = lean_ctor_get(x_250, 0);
lean_inc(x_290);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_291 = x_250;
} else {
 lean_dec_ref(x_250);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 1, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_290);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_293 = lean_ctor_get(x_248, 0);
lean_inc(x_293);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 x_294 = x_248;
} else {
 lean_dec_ref(x_248);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(1, 1, 0);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_293);
return x_295;
}
}
else
{
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
x_205 = x_6;
x_206 = x_7;
x_207 = x_8;
x_208 = x_9;
x_209 = x_10;
x_210 = x_11;
x_211 = x_12;
x_212 = x_13;
x_213 = x_14;
x_214 = lean_box(0);
goto block_244;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_204);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_296 = lean_ctor_get(x_245, 0);
lean_inc(x_296);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 x_297 = x_245;
} else {
 lean_dec_ref(x_245);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(1, 1, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_296);
return x_298;
}
}
block_244:
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_204, 2);
lean_inc(x_215);
lean_dec(x_204);
x_216 = l_Lean_mkNatLit(x_215);
x_217 = l_Lean_Meta_Sym_shareCommon___redArg(x_216, x_209);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
lean_dec_ref(x_217);
x_219 = lean_unsigned_to_nat(0u);
x_220 = lean_box(0);
lean_inc(x_213);
lean_inc_ref(x_212);
lean_inc(x_211);
lean_inc_ref(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc_ref(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_218);
x_221 = lean_grind_internalize(x_218, x_219, x_220, x_205, x_206, x_207, x_208, x_209, x_210, x_211, x_212, x_213);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; 
lean_dec_ref(x_221);
lean_inc(x_213);
lean_inc_ref(x_212);
lean_inc(x_211);
lean_inc_ref(x_210);
lean_inc_ref(x_207);
lean_inc(x_205);
x_222 = lean_grind_mk_eq_proof(x_39, x_43, x_205, x_206, x_207, x_208, x_209, x_210, x_211, x_212, x_213);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
lean_dec_ref(x_222);
x_224 = l_Lean_Expr_appFn_x21(x_2);
lean_inc(x_213);
lean_inc_ref(x_212);
lean_inc(x_211);
lean_inc_ref(x_210);
x_225 = l_Lean_Meta_mkCongrArg(x_224, x_223, x_210, x_211, x_212, x_213);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_dec_ref(x_225);
lean_inc(x_213);
lean_inc_ref(x_212);
lean_inc(x_211);
lean_inc_ref(x_210);
lean_inc(x_218);
lean_inc_ref(x_2);
x_227 = l_Lean_Meta_mkEq(x_2, x_218, x_210, x_211, x_212, x_213);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
lean_dec_ref(x_227);
x_229 = l_Lean_Meta_mkExpectedPropHint(x_226, x_228);
x_230 = 0;
x_231 = l_Lean_Meta_Grind_pushEqCore___redArg(x_2, x_218, x_229, x_230, x_205, x_207, x_210, x_211, x_212, x_213);
lean_dec_ref(x_207);
lean_dec(x_205);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_226);
lean_dec(x_218);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec_ref(x_210);
lean_dec_ref(x_207);
lean_dec(x_205);
lean_dec_ref(x_2);
x_232 = lean_ctor_get(x_227, 0);
lean_inc(x_232);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 x_233 = x_227;
} else {
 lean_dec_ref(x_227);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 1, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_232);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_218);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec_ref(x_210);
lean_dec_ref(x_207);
lean_dec(x_205);
lean_dec_ref(x_2);
x_235 = lean_ctor_get(x_225, 0);
lean_inc(x_235);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 x_236 = x_225;
} else {
 lean_dec_ref(x_225);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 1, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_235);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_218);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec_ref(x_210);
lean_dec_ref(x_207);
lean_dec(x_205);
lean_dec_ref(x_2);
x_238 = lean_ctor_get(x_222, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 x_239 = x_222;
} else {
 lean_dec_ref(x_222);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 1, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_238);
return x_240;
}
}
else
{
lean_dec(x_218);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec_ref(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec_ref(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec_ref(x_2);
return x_221;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec_ref(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec_ref(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec_ref(x_2);
x_241 = lean_ctor_get(x_217, 0);
lean_inc(x_241);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 x_242 = x_217;
} else {
 lean_dec_ref(x_217);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 1, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_241);
return x_243;
}
}
}
else
{
lean_object* x_299; lean_object* x_300; 
lean_dec(x_203);
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_299 = lean_box(0);
x_300 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_300, 0, x_299);
return x_300;
}
}
}
else
{
uint8_t x_301; 
lean_dec_ref(x_43);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_301 = !lean_is_exclusive(x_90);
if (x_301 == 0)
{
return x_90;
}
else
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_90, 0);
lean_inc(x_302);
lean_dec(x_90);
x_303 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_303, 0, x_302);
return x_303;
}
}
}
block_88:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_inc(x_47);
x_61 = l_Lean_mkConst(x_47, x_49);
x_62 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0;
x_63 = l_Lean_Expr_getAppNumArgs(x_48);
lean_inc(x_63);
x_64 = lean_mk_array(x_63, x_62);
x_65 = lean_nat_sub(x_63, x_35);
lean_dec(x_63);
x_66 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_48, x_64, x_65);
x_67 = l_Lean_mkAppN(x_61, x_66);
lean_dec_ref(x_66);
x_68 = l_Lean_Expr_app___override(x_67, x_39);
x_69 = l_Lean_Expr_getAppNumArgs(x_50);
lean_inc(x_69);
x_70 = lean_mk_array(x_69, x_62);
x_71 = lean_nat_sub(x_69, x_35);
lean_dec(x_69);
x_72 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_50, x_70, x_71);
x_73 = l_Lean_mkAppN(x_68, x_72);
lean_dec_ref(x_72);
x_74 = l_Lean_Expr_app___override(x_73, x_43);
lean_inc(x_59);
lean_inc_ref(x_58);
lean_inc(x_57);
lean_inc_ref(x_56);
lean_inc_ref(x_74);
x_75 = lean_infer_type(x_74, x_56, x_57, x_58, x_59);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
if (lean_is_scalar(x_29)) {
 x_77 = lean_alloc_ctor(0, 1, 0);
} else {
 x_77 = x_29;
 lean_ctor_set_tag(x_77, 0);
}
lean_ctor_set(x_77, 0, x_47);
if (lean_is_scalar(x_24)) {
 x_78 = lean_alloc_ctor(7, 1, 0);
} else {
 x_78 = x_24;
 lean_ctor_set_tag(x_78, 7);
}
lean_ctor_set(x_78, 0, x_77);
x_79 = l_Lean_Meta_Grind_addNewRawFact(x_74, x_76, x_46, x_78, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_59);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
x_82 = lean_box(0);
lean_ctor_set(x_79, 0, x_82);
return x_79;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_79);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
else
{
return x_79;
}
}
else
{
uint8_t x_85; 
lean_dec_ref(x_74);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_29);
lean_dec(x_24);
x_85 = !lean_is_exclusive(x_75);
if (x_85 == 0)
{
return x_75;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_75, 0);
lean_inc(x_86);
lean_dec(x_75);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
}
else
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; uint8_t x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_304 = lean_ctor_get(x_40, 0);
lean_inc(x_304);
lean_dec(x_40);
x_305 = lean_ctor_get(x_304, 0);
lean_inc_ref(x_305);
x_306 = lean_ctor_get_uint8(x_304, sizeof(void*)*11 + 2);
x_307 = lean_ctor_get_uint8(x_304, sizeof(void*)*11 + 4);
lean_dec(x_304);
if (x_306 == 0)
{
lean_object* x_349; lean_object* x_350; 
lean_dec_ref(x_305);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_349 = lean_box(0);
x_350 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_350, 0, x_349);
return x_350;
}
else
{
lean_object* x_351; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_305);
x_351 = l_Lean_Meta_isConstructorApp_x3f(x_305, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 x_353 = x_351;
} else {
 lean_dec_ref(x_351);
 x_353 = lean_box(0);
}
if (lean_obj_tag(x_352) == 1)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_353);
x_354 = lean_ctor_get(x_352, 0);
lean_inc(x_354);
lean_dec_ref(x_352);
if (x_307 == 0)
{
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
x_355 = x_6;
x_356 = x_7;
x_357 = x_8;
x_358 = x_9;
x_359 = x_10;
x_360 = x_11;
x_361 = x_12;
x_362 = x_13;
x_363 = x_14;
x_364 = lean_box(0);
goto block_394;
}
else
{
lean_object* x_395; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_305);
lean_inc(x_39);
x_395 = l_Lean_Meta_Grind_hasSameType(x_39, x_305, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; uint8_t x_397; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
lean_dec_ref(x_395);
x_397 = lean_unbox(x_396);
lean_dec(x_396);
if (x_397 == 0)
{
lean_object* x_398; 
lean_dec(x_354);
lean_dec_ref(x_2);
x_398 = l_Lean_Meta_Grind_getGeneration___redArg(x_39, x_6);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
lean_dec_ref(x_398);
x_400 = l_Lean_Meta_Grind_getGeneration___redArg(x_305, x_6);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; uint8_t x_439; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
lean_dec_ref(x_400);
x_439 = lean_nat_dec_le(x_399, x_401);
if (x_439 == 0)
{
lean_dec(x_401);
x_402 = x_399;
goto block_438;
}
else
{
lean_dec(x_399);
x_402 = x_401;
goto block_438;
}
block_438:
{
lean_object* x_403; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_39);
x_403 = lean_infer_type(x_39, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
lean_dec_ref(x_403);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_405 = l_Lean_Meta_whnfD(x_404, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
lean_dec_ref(x_405);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_305);
x_407 = lean_infer_type(x_305, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
lean_dec_ref(x_407);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_409 = l_Lean_Meta_whnfD(x_408, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 x_411 = x_409;
} else {
 lean_dec_ref(x_409);
 x_411 = lean_box(0);
}
x_412 = lean_ctor_get(x_30, 0);
lean_inc(x_412);
lean_dec_ref(x_30);
lean_inc(x_34);
x_413 = l_Lean_Expr_isAppOfArity(x_406, x_412, x_34);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; 
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_410);
lean_dec(x_406);
lean_dec(x_402);
lean_dec_ref(x_305);
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_24);
x_414 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4;
x_415 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_414, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_415;
}
else
{
uint8_t x_416; 
x_416 = l_Lean_Expr_isAppOfArity(x_410, x_412, x_34);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; 
lean_dec(x_412);
lean_dec(x_410);
lean_dec(x_406);
lean_dec(x_402);
lean_dec_ref(x_305);
lean_dec(x_39);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_417 = lean_box(0);
if (lean_is_scalar(x_411)) {
 x_418 = lean_alloc_ctor(0, 1, 0);
} else {
 x_418 = x_411;
}
lean_ctor_set(x_418, 0, x_417);
return x_418;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
lean_dec(x_411);
x_419 = lean_st_ref_get(x_14);
x_420 = lean_ctor_get(x_419, 0);
lean_inc_ref(x_420);
lean_dec(x_419);
x_421 = l_Lean_Expr_getAppFn(x_406);
x_422 = l_Lean_Expr_constLevels_x21(x_421);
lean_dec_ref(x_421);
x_423 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_412);
x_424 = l_Lean_Environment_containsOnBranch(x_420, x_423);
if (x_424 == 0)
{
lean_object* x_425; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_423);
x_425 = l_Lean_executeReservedNameAction(x_423, x_13, x_14);
if (lean_obj_tag(x_425) == 0)
{
lean_dec_ref(x_425);
x_308 = x_402;
x_309 = x_423;
x_310 = x_406;
x_311 = x_422;
x_312 = x_410;
x_313 = x_6;
x_314 = x_7;
x_315 = x_8;
x_316 = x_9;
x_317 = x_10;
x_318 = x_11;
x_319 = x_12;
x_320 = x_13;
x_321 = x_14;
x_322 = lean_box(0);
goto block_348;
}
else
{
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_410);
lean_dec(x_406);
lean_dec(x_402);
lean_dec_ref(x_305);
lean_dec(x_39);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_425;
}
}
else
{
x_308 = x_402;
x_309 = x_423;
x_310 = x_406;
x_311 = x_422;
x_312 = x_410;
x_313 = x_6;
x_314 = x_7;
x_315 = x_8;
x_316 = x_9;
x_317 = x_10;
x_318 = x_11;
x_319 = x_12;
x_320 = x_13;
x_321 = x_14;
x_322 = lean_box(0);
goto block_348;
}
}
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_406);
lean_dec(x_402);
lean_dec_ref(x_305);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_426 = lean_ctor_get(x_409, 0);
lean_inc(x_426);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 x_427 = x_409;
} else {
 lean_dec_ref(x_409);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_427)) {
 x_428 = lean_alloc_ctor(1, 1, 0);
} else {
 x_428 = x_427;
}
lean_ctor_set(x_428, 0, x_426);
return x_428;
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_406);
lean_dec(x_402);
lean_dec_ref(x_305);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_429 = lean_ctor_get(x_407, 0);
lean_inc(x_429);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 x_430 = x_407;
} else {
 lean_dec_ref(x_407);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 1, 0);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_429);
return x_431;
}
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
lean_dec(x_402);
lean_dec_ref(x_305);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_432 = lean_ctor_get(x_405, 0);
lean_inc(x_432);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 x_433 = x_405;
} else {
 lean_dec_ref(x_405);
 x_433 = lean_box(0);
}
if (lean_is_scalar(x_433)) {
 x_434 = lean_alloc_ctor(1, 1, 0);
} else {
 x_434 = x_433;
}
lean_ctor_set(x_434, 0, x_432);
return x_434;
}
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_402);
lean_dec_ref(x_305);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_435 = lean_ctor_get(x_403, 0);
lean_inc(x_435);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 x_436 = x_403;
} else {
 lean_dec_ref(x_403);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 1, 0);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_435);
return x_437;
}
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_399);
lean_dec_ref(x_305);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_440 = lean_ctor_get(x_400, 0);
lean_inc(x_440);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 x_441 = x_400;
} else {
 lean_dec_ref(x_400);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(1, 1, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_440);
return x_442;
}
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec_ref(x_305);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_443 = lean_ctor_get(x_398, 0);
lean_inc(x_443);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 x_444 = x_398;
} else {
 lean_dec_ref(x_398);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(1, 1, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_443);
return x_445;
}
}
else
{
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
x_355 = x_6;
x_356 = x_7;
x_357 = x_8;
x_358 = x_9;
x_359 = x_10;
x_360 = x_11;
x_361 = x_12;
x_362 = x_13;
x_363 = x_14;
x_364 = lean_box(0);
goto block_394;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_354);
lean_dec_ref(x_305);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_446 = lean_ctor_get(x_395, 0);
lean_inc(x_446);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 x_447 = x_395;
} else {
 lean_dec_ref(x_395);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 1, 0);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_446);
return x_448;
}
}
block_394:
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_354, 2);
lean_inc(x_365);
lean_dec(x_354);
x_366 = l_Lean_mkNatLit(x_365);
x_367 = l_Lean_Meta_Sym_shareCommon___redArg(x_366, x_359);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
lean_dec_ref(x_367);
x_369 = lean_unsigned_to_nat(0u);
x_370 = lean_box(0);
lean_inc(x_363);
lean_inc_ref(x_362);
lean_inc(x_361);
lean_inc_ref(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_inc_ref(x_357);
lean_inc(x_356);
lean_inc(x_355);
lean_inc(x_368);
x_371 = lean_grind_internalize(x_368, x_369, x_370, x_355, x_356, x_357, x_358, x_359, x_360, x_361, x_362, x_363);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; 
lean_dec_ref(x_371);
lean_inc(x_363);
lean_inc_ref(x_362);
lean_inc(x_361);
lean_inc_ref(x_360);
lean_inc_ref(x_357);
lean_inc(x_355);
x_372 = lean_grind_mk_eq_proof(x_39, x_305, x_355, x_356, x_357, x_358, x_359, x_360, x_361, x_362, x_363);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
lean_dec_ref(x_372);
x_374 = l_Lean_Expr_appFn_x21(x_2);
lean_inc(x_363);
lean_inc_ref(x_362);
lean_inc(x_361);
lean_inc_ref(x_360);
x_375 = l_Lean_Meta_mkCongrArg(x_374, x_373, x_360, x_361, x_362, x_363);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
lean_dec_ref(x_375);
lean_inc(x_363);
lean_inc_ref(x_362);
lean_inc(x_361);
lean_inc_ref(x_360);
lean_inc(x_368);
lean_inc_ref(x_2);
x_377 = l_Lean_Meta_mkEq(x_2, x_368, x_360, x_361, x_362, x_363);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; uint8_t x_380; lean_object* x_381; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
lean_dec_ref(x_377);
x_379 = l_Lean_Meta_mkExpectedPropHint(x_376, x_378);
x_380 = 0;
x_381 = l_Lean_Meta_Grind_pushEqCore___redArg(x_2, x_368, x_379, x_380, x_355, x_357, x_360, x_361, x_362, x_363);
lean_dec_ref(x_357);
lean_dec(x_355);
return x_381;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_376);
lean_dec(x_368);
lean_dec(x_363);
lean_dec_ref(x_362);
lean_dec(x_361);
lean_dec_ref(x_360);
lean_dec_ref(x_357);
lean_dec(x_355);
lean_dec_ref(x_2);
x_382 = lean_ctor_get(x_377, 0);
lean_inc(x_382);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 x_383 = x_377;
} else {
 lean_dec_ref(x_377);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 1, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_382);
return x_384;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
lean_dec(x_368);
lean_dec(x_363);
lean_dec_ref(x_362);
lean_dec(x_361);
lean_dec_ref(x_360);
lean_dec_ref(x_357);
lean_dec(x_355);
lean_dec_ref(x_2);
x_385 = lean_ctor_get(x_375, 0);
lean_inc(x_385);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 x_386 = x_375;
} else {
 lean_dec_ref(x_375);
 x_386 = lean_box(0);
}
if (lean_is_scalar(x_386)) {
 x_387 = lean_alloc_ctor(1, 1, 0);
} else {
 x_387 = x_386;
}
lean_ctor_set(x_387, 0, x_385);
return x_387;
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_368);
lean_dec(x_363);
lean_dec_ref(x_362);
lean_dec(x_361);
lean_dec_ref(x_360);
lean_dec_ref(x_357);
lean_dec(x_355);
lean_dec_ref(x_2);
x_388 = lean_ctor_get(x_372, 0);
lean_inc(x_388);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 x_389 = x_372;
} else {
 lean_dec_ref(x_372);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(1, 1, 0);
} else {
 x_390 = x_389;
}
lean_ctor_set(x_390, 0, x_388);
return x_390;
}
}
else
{
lean_dec(x_368);
lean_dec(x_363);
lean_dec_ref(x_362);
lean_dec(x_361);
lean_dec_ref(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec_ref(x_357);
lean_dec(x_356);
lean_dec(x_355);
lean_dec_ref(x_305);
lean_dec(x_39);
lean_dec_ref(x_2);
return x_371;
}
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_363);
lean_dec_ref(x_362);
lean_dec(x_361);
lean_dec_ref(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec_ref(x_357);
lean_dec(x_356);
lean_dec(x_355);
lean_dec_ref(x_305);
lean_dec(x_39);
lean_dec_ref(x_2);
x_391 = lean_ctor_get(x_367, 0);
lean_inc(x_391);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 x_392 = x_367;
} else {
 lean_dec_ref(x_367);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 1, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_391);
return x_393;
}
}
}
else
{
lean_object* x_449; lean_object* x_450; 
lean_dec(x_352);
lean_dec_ref(x_305);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_449 = lean_box(0);
if (lean_is_scalar(x_353)) {
 x_450 = lean_alloc_ctor(0, 1, 0);
} else {
 x_450 = x_353;
}
lean_ctor_set(x_450, 0, x_449);
return x_450;
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec_ref(x_305);
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_451 = lean_ctor_get(x_351, 0);
lean_inc(x_451);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 x_452 = x_351;
} else {
 lean_dec_ref(x_351);
 x_452 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(1, 1, 0);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_451);
return x_453;
}
}
block_348:
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_inc(x_309);
x_323 = l_Lean_mkConst(x_309, x_311);
x_324 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0;
x_325 = l_Lean_Expr_getAppNumArgs(x_310);
lean_inc(x_325);
x_326 = lean_mk_array(x_325, x_324);
x_327 = lean_nat_sub(x_325, x_35);
lean_dec(x_325);
x_328 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_310, x_326, x_327);
x_329 = l_Lean_mkAppN(x_323, x_328);
lean_dec_ref(x_328);
x_330 = l_Lean_Expr_app___override(x_329, x_39);
x_331 = l_Lean_Expr_getAppNumArgs(x_312);
lean_inc(x_331);
x_332 = lean_mk_array(x_331, x_324);
x_333 = lean_nat_sub(x_331, x_35);
lean_dec(x_331);
x_334 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_312, x_332, x_333);
x_335 = l_Lean_mkAppN(x_330, x_334);
lean_dec_ref(x_334);
x_336 = l_Lean_Expr_app___override(x_335, x_305);
lean_inc(x_321);
lean_inc_ref(x_320);
lean_inc(x_319);
lean_inc_ref(x_318);
lean_inc_ref(x_336);
x_337 = lean_infer_type(x_336, x_318, x_319, x_320, x_321);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
lean_dec_ref(x_337);
if (lean_is_scalar(x_29)) {
 x_339 = lean_alloc_ctor(0, 1, 0);
} else {
 x_339 = x_29;
 lean_ctor_set_tag(x_339, 0);
}
lean_ctor_set(x_339, 0, x_309);
if (lean_is_scalar(x_24)) {
 x_340 = lean_alloc_ctor(7, 1, 0);
} else {
 x_340 = x_24;
 lean_ctor_set_tag(x_340, 7);
}
lean_ctor_set(x_340, 0, x_339);
x_341 = l_Lean_Meta_Grind_addNewRawFact(x_336, x_338, x_308, x_340, x_313, x_314, x_315, x_316, x_317, x_318, x_319, x_320, x_321);
lean_dec(x_317);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec(x_313);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 x_342 = x_341;
} else {
 lean_dec_ref(x_341);
 x_342 = lean_box(0);
}
x_343 = lean_box(0);
if (lean_is_scalar(x_342)) {
 x_344 = lean_alloc_ctor(0, 1, 0);
} else {
 x_344 = x_342;
}
lean_ctor_set(x_344, 0, x_343);
return x_344;
}
else
{
return x_341;
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec_ref(x_336);
lean_dec(x_321);
lean_dec_ref(x_320);
lean_dec(x_319);
lean_dec_ref(x_318);
lean_dec(x_317);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_309);
lean_dec(x_308);
lean_dec(x_29);
lean_dec(x_24);
x_345 = lean_ctor_get(x_337, 0);
lean_inc(x_345);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 x_346 = x_337;
} else {
 lean_dec_ref(x_337);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(1, 1, 0);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_345);
return x_347;
}
}
}
}
else
{
uint8_t x_454; 
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_454 = !lean_is_exclusive(x_40);
if (x_454 == 0)
{
return x_40;
}
else
{
lean_object* x_455; lean_object* x_456; 
x_455 = lean_ctor_get(x_40, 0);
lean_inc(x_455);
lean_dec(x_40);
x_456 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_456, 0, x_455);
return x_456;
}
}
}
}
else
{
lean_object* x_457; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_457 = lean_box(0);
lean_ctor_set(x_25, 0, x_457);
return x_25;
}
}
else
{
lean_object* x_458; 
x_458 = lean_ctor_get(x_25, 0);
lean_inc(x_458);
lean_dec(x_25);
if (lean_obj_tag(x_458) == 1)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; uint8_t x_468; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 x_460 = x_458;
} else {
 lean_dec_ref(x_458);
 x_460 = lean_box(0);
}
x_461 = lean_ctor_get(x_459, 0);
lean_inc_ref(x_461);
x_462 = lean_ctor_get(x_459, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_459, 2);
lean_inc(x_463);
lean_dec(x_459);
x_464 = lean_array_get_size(x_4);
x_465 = lean_nat_add(x_462, x_463);
lean_dec(x_463);
lean_dec(x_462);
x_466 = lean_unsigned_to_nat(1u);
x_467 = lean_nat_add(x_465, x_466);
x_468 = lean_nat_dec_eq(x_464, x_467);
lean_dec(x_467);
if (x_468 == 0)
{
lean_object* x_469; lean_object* x_470; 
lean_dec(x_465);
lean_dec_ref(x_461);
lean_dec(x_460);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_469 = lean_box(0);
x_470 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_470, 0, x_469);
return x_470;
}
else
{
lean_object* x_471; lean_object* x_472; 
x_471 = l_Array_back_x21___redArg(x_1, x_4);
lean_dec_ref(x_4);
lean_inc(x_471);
x_472 = l_Lean_Meta_Grind_getRootENode___redArg(x_471, x_6, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; uint8_t x_476; uint8_t x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 x_474 = x_472;
} else {
 lean_dec_ref(x_472);
 x_474 = lean_box(0);
}
x_475 = lean_ctor_get(x_473, 0);
lean_inc_ref(x_475);
x_476 = lean_ctor_get_uint8(x_473, sizeof(void*)*11 + 2);
x_477 = lean_ctor_get_uint8(x_473, sizeof(void*)*11 + 4);
lean_dec(x_473);
if (x_476 == 0)
{
lean_object* x_519; lean_object* x_520; 
lean_dec_ref(x_475);
lean_dec(x_471);
lean_dec(x_465);
lean_dec_ref(x_461);
lean_dec(x_460);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_519 = lean_box(0);
if (lean_is_scalar(x_474)) {
 x_520 = lean_alloc_ctor(0, 1, 0);
} else {
 x_520 = x_474;
}
lean_ctor_set(x_520, 0, x_519);
return x_520;
}
else
{
lean_object* x_521; 
lean_dec(x_474);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_475);
x_521 = l_Lean_Meta_isConstructorApp_x3f(x_475, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_521) == 0)
{
lean_object* x_522; lean_object* x_523; 
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 x_523 = x_521;
} else {
 lean_dec_ref(x_521);
 x_523 = lean_box(0);
}
if (lean_obj_tag(x_522) == 1)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
lean_dec(x_523);
x_524 = lean_ctor_get(x_522, 0);
lean_inc(x_524);
lean_dec_ref(x_522);
if (x_477 == 0)
{
lean_dec(x_465);
lean_dec_ref(x_461);
lean_dec(x_460);
lean_dec(x_24);
x_525 = x_6;
x_526 = x_7;
x_527 = x_8;
x_528 = x_9;
x_529 = x_10;
x_530 = x_11;
x_531 = x_12;
x_532 = x_13;
x_533 = x_14;
x_534 = lean_box(0);
goto block_564;
}
else
{
lean_object* x_565; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_475);
lean_inc(x_471);
x_565 = l_Lean_Meta_Grind_hasSameType(x_471, x_475, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_565) == 0)
{
lean_object* x_566; uint8_t x_567; 
x_566 = lean_ctor_get(x_565, 0);
lean_inc(x_566);
lean_dec_ref(x_565);
x_567 = lean_unbox(x_566);
lean_dec(x_566);
if (x_567 == 0)
{
lean_object* x_568; 
lean_dec(x_524);
lean_dec_ref(x_2);
x_568 = l_Lean_Meta_Grind_getGeneration___redArg(x_471, x_6);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; lean_object* x_570; 
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
lean_dec_ref(x_568);
x_570 = l_Lean_Meta_Grind_getGeneration___redArg(x_475, x_6);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; uint8_t x_609; 
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
lean_dec_ref(x_570);
x_609 = lean_nat_dec_le(x_569, x_571);
if (x_609 == 0)
{
lean_dec(x_571);
x_572 = x_569;
goto block_608;
}
else
{
lean_dec(x_569);
x_572 = x_571;
goto block_608;
}
block_608:
{
lean_object* x_573; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_471);
x_573 = lean_infer_type(x_471, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; 
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
lean_dec_ref(x_573);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_575 = l_Lean_Meta_whnfD(x_574, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; lean_object* x_577; 
x_576 = lean_ctor_get(x_575, 0);
lean_inc(x_576);
lean_dec_ref(x_575);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_475);
x_577 = lean_infer_type(x_475, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; 
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
lean_dec_ref(x_577);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_579 = l_Lean_Meta_whnfD(x_578, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; uint8_t x_583; 
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 x_581 = x_579;
} else {
 lean_dec_ref(x_579);
 x_581 = lean_box(0);
}
x_582 = lean_ctor_get(x_461, 0);
lean_inc(x_582);
lean_dec_ref(x_461);
lean_inc(x_465);
x_583 = l_Lean_Expr_isAppOfArity(x_576, x_582, x_465);
if (x_583 == 0)
{
lean_object* x_584; lean_object* x_585; 
lean_dec(x_582);
lean_dec(x_581);
lean_dec(x_580);
lean_dec(x_576);
lean_dec(x_572);
lean_dec_ref(x_475);
lean_dec(x_471);
lean_dec(x_465);
lean_dec(x_460);
lean_dec(x_24);
x_584 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4;
x_585 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_584, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_585;
}
else
{
uint8_t x_586; 
x_586 = l_Lean_Expr_isAppOfArity(x_580, x_582, x_465);
if (x_586 == 0)
{
lean_object* x_587; lean_object* x_588; 
lean_dec(x_582);
lean_dec(x_580);
lean_dec(x_576);
lean_dec(x_572);
lean_dec_ref(x_475);
lean_dec(x_471);
lean_dec(x_460);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_587 = lean_box(0);
if (lean_is_scalar(x_581)) {
 x_588 = lean_alloc_ctor(0, 1, 0);
} else {
 x_588 = x_581;
}
lean_ctor_set(x_588, 0, x_587);
return x_588;
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; uint8_t x_594; 
lean_dec(x_581);
x_589 = lean_st_ref_get(x_14);
x_590 = lean_ctor_get(x_589, 0);
lean_inc_ref(x_590);
lean_dec(x_589);
x_591 = l_Lean_Expr_getAppFn(x_576);
x_592 = l_Lean_Expr_constLevels_x21(x_591);
lean_dec_ref(x_591);
x_593 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_582);
x_594 = l_Lean_Environment_containsOnBranch(x_590, x_593);
if (x_594 == 0)
{
lean_object* x_595; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_593);
x_595 = l_Lean_executeReservedNameAction(x_593, x_13, x_14);
if (lean_obj_tag(x_595) == 0)
{
lean_dec_ref(x_595);
x_478 = x_572;
x_479 = x_593;
x_480 = x_576;
x_481 = x_592;
x_482 = x_580;
x_483 = x_6;
x_484 = x_7;
x_485 = x_8;
x_486 = x_9;
x_487 = x_10;
x_488 = x_11;
x_489 = x_12;
x_490 = x_13;
x_491 = x_14;
x_492 = lean_box(0);
goto block_518;
}
else
{
lean_dec(x_593);
lean_dec(x_592);
lean_dec(x_580);
lean_dec(x_576);
lean_dec(x_572);
lean_dec_ref(x_475);
lean_dec(x_471);
lean_dec(x_460);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_595;
}
}
else
{
x_478 = x_572;
x_479 = x_593;
x_480 = x_576;
x_481 = x_592;
x_482 = x_580;
x_483 = x_6;
x_484 = x_7;
x_485 = x_8;
x_486 = x_9;
x_487 = x_10;
x_488 = x_11;
x_489 = x_12;
x_490 = x_13;
x_491 = x_14;
x_492 = lean_box(0);
goto block_518;
}
}
}
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; 
lean_dec(x_576);
lean_dec(x_572);
lean_dec_ref(x_475);
lean_dec(x_471);
lean_dec(x_465);
lean_dec_ref(x_461);
lean_dec(x_460);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_596 = lean_ctor_get(x_579, 0);
lean_inc(x_596);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 x_597 = x_579;
} else {
 lean_dec_ref(x_579);
 x_597 = lean_box(0);
}
if (lean_is_scalar(x_597)) {
 x_598 = lean_alloc_ctor(1, 1, 0);
} else {
 x_598 = x_597;
}
lean_ctor_set(x_598, 0, x_596);
return x_598;
}
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; 
lean_dec(x_576);
lean_dec(x_572);
lean_dec_ref(x_475);
lean_dec(x_471);
lean_dec(x_465);
lean_dec_ref(x_461);
lean_dec(x_460);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_599 = lean_ctor_get(x_577, 0);
lean_inc(x_599);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 x_600 = x_577;
} else {
 lean_dec_ref(x_577);
 x_600 = lean_box(0);
}
if (lean_is_scalar(x_600)) {
 x_601 = lean_alloc_ctor(1, 1, 0);
} else {
 x_601 = x_600;
}
lean_ctor_set(x_601, 0, x_599);
return x_601;
}
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
lean_dec(x_572);
lean_dec_ref(x_475);
lean_dec(x_471);
lean_dec(x_465);
lean_dec_ref(x_461);
lean_dec(x_460);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_602 = lean_ctor_get(x_575, 0);
lean_inc(x_602);
if (lean_is_exclusive(x_575)) {
 lean_ctor_release(x_575, 0);
 x_603 = x_575;
} else {
 lean_dec_ref(x_575);
 x_603 = lean_box(0);
}
if (lean_is_scalar(x_603)) {
 x_604 = lean_alloc_ctor(1, 1, 0);
} else {
 x_604 = x_603;
}
lean_ctor_set(x_604, 0, x_602);
return x_604;
}
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; 
lean_dec(x_572);
lean_dec_ref(x_475);
lean_dec(x_471);
lean_dec(x_465);
lean_dec_ref(x_461);
lean_dec(x_460);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_605 = lean_ctor_get(x_573, 0);
lean_inc(x_605);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 x_606 = x_573;
} else {
 lean_dec_ref(x_573);
 x_606 = lean_box(0);
}
if (lean_is_scalar(x_606)) {
 x_607 = lean_alloc_ctor(1, 1, 0);
} else {
 x_607 = x_606;
}
lean_ctor_set(x_607, 0, x_605);
return x_607;
}
}
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec(x_569);
lean_dec_ref(x_475);
lean_dec(x_471);
lean_dec(x_465);
lean_dec_ref(x_461);
lean_dec(x_460);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_610 = lean_ctor_get(x_570, 0);
lean_inc(x_610);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 x_611 = x_570;
} else {
 lean_dec_ref(x_570);
 x_611 = lean_box(0);
}
if (lean_is_scalar(x_611)) {
 x_612 = lean_alloc_ctor(1, 1, 0);
} else {
 x_612 = x_611;
}
lean_ctor_set(x_612, 0, x_610);
return x_612;
}
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
lean_dec_ref(x_475);
lean_dec(x_471);
lean_dec(x_465);
lean_dec_ref(x_461);
lean_dec(x_460);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_613 = lean_ctor_get(x_568, 0);
lean_inc(x_613);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 x_614 = x_568;
} else {
 lean_dec_ref(x_568);
 x_614 = lean_box(0);
}
if (lean_is_scalar(x_614)) {
 x_615 = lean_alloc_ctor(1, 1, 0);
} else {
 x_615 = x_614;
}
lean_ctor_set(x_615, 0, x_613);
return x_615;
}
}
else
{
lean_dec(x_465);
lean_dec_ref(x_461);
lean_dec(x_460);
lean_dec(x_24);
x_525 = x_6;
x_526 = x_7;
x_527 = x_8;
x_528 = x_9;
x_529 = x_10;
x_530 = x_11;
x_531 = x_12;
x_532 = x_13;
x_533 = x_14;
x_534 = lean_box(0);
goto block_564;
}
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
lean_dec(x_524);
lean_dec_ref(x_475);
lean_dec(x_471);
lean_dec(x_465);
lean_dec_ref(x_461);
lean_dec(x_460);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_616 = lean_ctor_get(x_565, 0);
lean_inc(x_616);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 x_617 = x_565;
} else {
 lean_dec_ref(x_565);
 x_617 = lean_box(0);
}
if (lean_is_scalar(x_617)) {
 x_618 = lean_alloc_ctor(1, 1, 0);
} else {
 x_618 = x_617;
}
lean_ctor_set(x_618, 0, x_616);
return x_618;
}
}
block_564:
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_535 = lean_ctor_get(x_524, 2);
lean_inc(x_535);
lean_dec(x_524);
x_536 = l_Lean_mkNatLit(x_535);
x_537 = l_Lean_Meta_Sym_shareCommon___redArg(x_536, x_529);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
lean_dec_ref(x_537);
x_539 = lean_unsigned_to_nat(0u);
x_540 = lean_box(0);
lean_inc(x_533);
lean_inc_ref(x_532);
lean_inc(x_531);
lean_inc_ref(x_530);
lean_inc(x_529);
lean_inc(x_528);
lean_inc_ref(x_527);
lean_inc(x_526);
lean_inc(x_525);
lean_inc(x_538);
x_541 = lean_grind_internalize(x_538, x_539, x_540, x_525, x_526, x_527, x_528, x_529, x_530, x_531, x_532, x_533);
if (lean_obj_tag(x_541) == 0)
{
lean_object* x_542; 
lean_dec_ref(x_541);
lean_inc(x_533);
lean_inc_ref(x_532);
lean_inc(x_531);
lean_inc_ref(x_530);
lean_inc_ref(x_527);
lean_inc(x_525);
x_542 = lean_grind_mk_eq_proof(x_471, x_475, x_525, x_526, x_527, x_528, x_529, x_530, x_531, x_532, x_533);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
lean_dec_ref(x_542);
x_544 = l_Lean_Expr_appFn_x21(x_2);
lean_inc(x_533);
lean_inc_ref(x_532);
lean_inc(x_531);
lean_inc_ref(x_530);
x_545 = l_Lean_Meta_mkCongrArg(x_544, x_543, x_530, x_531, x_532, x_533);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; 
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
lean_dec_ref(x_545);
lean_inc(x_533);
lean_inc_ref(x_532);
lean_inc(x_531);
lean_inc_ref(x_530);
lean_inc(x_538);
lean_inc_ref(x_2);
x_547 = l_Lean_Meta_mkEq(x_2, x_538, x_530, x_531, x_532, x_533);
if (lean_obj_tag(x_547) == 0)
{
lean_object* x_548; lean_object* x_549; uint8_t x_550; lean_object* x_551; 
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
lean_dec_ref(x_547);
x_549 = l_Lean_Meta_mkExpectedPropHint(x_546, x_548);
x_550 = 0;
x_551 = l_Lean_Meta_Grind_pushEqCore___redArg(x_2, x_538, x_549, x_550, x_525, x_527, x_530, x_531, x_532, x_533);
lean_dec_ref(x_527);
lean_dec(x_525);
return x_551;
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
lean_dec(x_546);
lean_dec(x_538);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec_ref(x_527);
lean_dec(x_525);
lean_dec_ref(x_2);
x_552 = lean_ctor_get(x_547, 0);
lean_inc(x_552);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 x_553 = x_547;
} else {
 lean_dec_ref(x_547);
 x_553 = lean_box(0);
}
if (lean_is_scalar(x_553)) {
 x_554 = lean_alloc_ctor(1, 1, 0);
} else {
 x_554 = x_553;
}
lean_ctor_set(x_554, 0, x_552);
return x_554;
}
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec(x_538);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec_ref(x_527);
lean_dec(x_525);
lean_dec_ref(x_2);
x_555 = lean_ctor_get(x_545, 0);
lean_inc(x_555);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 x_556 = x_545;
} else {
 lean_dec_ref(x_545);
 x_556 = lean_box(0);
}
if (lean_is_scalar(x_556)) {
 x_557 = lean_alloc_ctor(1, 1, 0);
} else {
 x_557 = x_556;
}
lean_ctor_set(x_557, 0, x_555);
return x_557;
}
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; 
lean_dec(x_538);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec_ref(x_527);
lean_dec(x_525);
lean_dec_ref(x_2);
x_558 = lean_ctor_get(x_542, 0);
lean_inc(x_558);
if (lean_is_exclusive(x_542)) {
 lean_ctor_release(x_542, 0);
 x_559 = x_542;
} else {
 lean_dec_ref(x_542);
 x_559 = lean_box(0);
}
if (lean_is_scalar(x_559)) {
 x_560 = lean_alloc_ctor(1, 1, 0);
} else {
 x_560 = x_559;
}
lean_ctor_set(x_560, 0, x_558);
return x_560;
}
}
else
{
lean_dec(x_538);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec(x_529);
lean_dec(x_528);
lean_dec_ref(x_527);
lean_dec(x_526);
lean_dec(x_525);
lean_dec_ref(x_475);
lean_dec(x_471);
lean_dec_ref(x_2);
return x_541;
}
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec(x_529);
lean_dec(x_528);
lean_dec_ref(x_527);
lean_dec(x_526);
lean_dec(x_525);
lean_dec_ref(x_475);
lean_dec(x_471);
lean_dec_ref(x_2);
x_561 = lean_ctor_get(x_537, 0);
lean_inc(x_561);
if (lean_is_exclusive(x_537)) {
 lean_ctor_release(x_537, 0);
 x_562 = x_537;
} else {
 lean_dec_ref(x_537);
 x_562 = lean_box(0);
}
if (lean_is_scalar(x_562)) {
 x_563 = lean_alloc_ctor(1, 1, 0);
} else {
 x_563 = x_562;
}
lean_ctor_set(x_563, 0, x_561);
return x_563;
}
}
}
else
{
lean_object* x_619; lean_object* x_620; 
lean_dec(x_522);
lean_dec_ref(x_475);
lean_dec(x_471);
lean_dec(x_465);
lean_dec_ref(x_461);
lean_dec(x_460);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_619 = lean_box(0);
if (lean_is_scalar(x_523)) {
 x_620 = lean_alloc_ctor(0, 1, 0);
} else {
 x_620 = x_523;
}
lean_ctor_set(x_620, 0, x_619);
return x_620;
}
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; 
lean_dec_ref(x_475);
lean_dec(x_471);
lean_dec(x_465);
lean_dec_ref(x_461);
lean_dec(x_460);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_621 = lean_ctor_get(x_521, 0);
lean_inc(x_621);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 x_622 = x_521;
} else {
 lean_dec_ref(x_521);
 x_622 = lean_box(0);
}
if (lean_is_scalar(x_622)) {
 x_623 = lean_alloc_ctor(1, 1, 0);
} else {
 x_623 = x_622;
}
lean_ctor_set(x_623, 0, x_621);
return x_623;
}
}
block_518:
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_inc(x_479);
x_493 = l_Lean_mkConst(x_479, x_481);
x_494 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0;
x_495 = l_Lean_Expr_getAppNumArgs(x_480);
lean_inc(x_495);
x_496 = lean_mk_array(x_495, x_494);
x_497 = lean_nat_sub(x_495, x_466);
lean_dec(x_495);
x_498 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_480, x_496, x_497);
x_499 = l_Lean_mkAppN(x_493, x_498);
lean_dec_ref(x_498);
x_500 = l_Lean_Expr_app___override(x_499, x_471);
x_501 = l_Lean_Expr_getAppNumArgs(x_482);
lean_inc(x_501);
x_502 = lean_mk_array(x_501, x_494);
x_503 = lean_nat_sub(x_501, x_466);
lean_dec(x_501);
x_504 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_482, x_502, x_503);
x_505 = l_Lean_mkAppN(x_500, x_504);
lean_dec_ref(x_504);
x_506 = l_Lean_Expr_app___override(x_505, x_475);
lean_inc(x_491);
lean_inc_ref(x_490);
lean_inc(x_489);
lean_inc_ref(x_488);
lean_inc_ref(x_506);
x_507 = lean_infer_type(x_506, x_488, x_489, x_490, x_491);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
lean_dec_ref(x_507);
if (lean_is_scalar(x_460)) {
 x_509 = lean_alloc_ctor(0, 1, 0);
} else {
 x_509 = x_460;
 lean_ctor_set_tag(x_509, 0);
}
lean_ctor_set(x_509, 0, x_479);
if (lean_is_scalar(x_24)) {
 x_510 = lean_alloc_ctor(7, 1, 0);
} else {
 x_510 = x_24;
 lean_ctor_set_tag(x_510, 7);
}
lean_ctor_set(x_510, 0, x_509);
x_511 = l_Lean_Meta_Grind_addNewRawFact(x_506, x_508, x_478, x_510, x_483, x_484, x_485, x_486, x_487, x_488, x_489, x_490, x_491);
lean_dec(x_487);
lean_dec(x_486);
lean_dec_ref(x_485);
lean_dec(x_484);
lean_dec(x_483);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; 
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 x_512 = x_511;
} else {
 lean_dec_ref(x_511);
 x_512 = lean_box(0);
}
x_513 = lean_box(0);
if (lean_is_scalar(x_512)) {
 x_514 = lean_alloc_ctor(0, 1, 0);
} else {
 x_514 = x_512;
}
lean_ctor_set(x_514, 0, x_513);
return x_514;
}
else
{
return x_511;
}
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
lean_dec_ref(x_506);
lean_dec(x_491);
lean_dec_ref(x_490);
lean_dec(x_489);
lean_dec_ref(x_488);
lean_dec(x_487);
lean_dec(x_486);
lean_dec_ref(x_485);
lean_dec(x_484);
lean_dec(x_483);
lean_dec(x_479);
lean_dec(x_478);
lean_dec(x_460);
lean_dec(x_24);
x_515 = lean_ctor_get(x_507, 0);
lean_inc(x_515);
if (lean_is_exclusive(x_507)) {
 lean_ctor_release(x_507, 0);
 x_516 = x_507;
} else {
 lean_dec_ref(x_507);
 x_516 = lean_box(0);
}
if (lean_is_scalar(x_516)) {
 x_517 = lean_alloc_ctor(1, 1, 0);
} else {
 x_517 = x_516;
}
lean_ctor_set(x_517, 0, x_515);
return x_517;
}
}
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; 
lean_dec(x_471);
lean_dec(x_465);
lean_dec_ref(x_461);
lean_dec(x_460);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_624 = lean_ctor_get(x_472, 0);
lean_inc(x_624);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 x_625 = x_472;
} else {
 lean_dec_ref(x_472);
 x_625 = lean_box(0);
}
if (lean_is_scalar(x_625)) {
 x_626 = lean_alloc_ctor(1, 1, 0);
} else {
 x_626 = x_625;
}
lean_ctor_set(x_626, 0, x_624);
return x_626;
}
}
}
else
{
lean_object* x_627; lean_object* x_628; 
lean_dec(x_458);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_627 = lean_box(0);
x_628 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_628, 0, x_627);
return x_628;
}
}
}
else
{
uint8_t x_629; 
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_629 = !lean_is_exclusive(x_25);
if (x_629 == 0)
{
return x_25;
}
else
{
lean_object* x_630; lean_object* x_631; 
x_630 = lean_ctor_get(x_25, 0);
lean_inc(x_630);
lean_dec(x_25);
x_631 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_631, 0, x_630);
return x_631;
}
}
}
else
{
lean_object* x_632; lean_object* x_633; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_632 = lean_box(0);
x_633 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_633, 0, x_632);
return x_633;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = l_Lean_instInhabitedExpr;
x_13 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0;
x_14 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_14);
x_15 = lean_mk_array(x_14, x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_14, x_16);
lean_dec(x_14);
lean_inc_ref(x_1);
x_18 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(x_12, x_1, x_1, x_15, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_propagateCtorIdxUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_CtorIdxHInj(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorIdxHInj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0 = _init_l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0);
l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0 = _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1 = _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1);
l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2 = _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2);
l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3 = _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3);
l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4 = _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
