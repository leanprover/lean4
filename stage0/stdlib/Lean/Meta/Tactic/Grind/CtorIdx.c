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
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.Tactic.Grind.CtorIdx"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.Grind.propagateCtorIdxUp"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 162, .m_capacity = 162, .m_length = 161, .m_data = "assertion violation: aType.isAppOfArity indInfo.name (indInfo.numParams + indInfo.numIndices)\n      -- both types should be headed by the same type former\n      "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_isCtorIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
lean_object* l_Lean_executeReservedNameAction(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0);
x_14 = lean_panic_fn(x_13, x_1);
x_15 = lean_apply_11(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_15;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3));
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_unsigned_to_nat(37u);
x_4 = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2));
x_5 = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_17);
lean_dec_ref(x_2);
x_18 = lean_array_set(x_3, x_4, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_4, x_19);
lean_dec(x_4);
x_2 = x_16;
x_3 = x_18;
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_4);
x_22 = l_Lean_Expr_constName_x3f(x_2);
lean_dec_ref(x_2);
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
x_33 = lean_array_get_size(x_3);
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
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_38 = lean_box(0);
lean_ctor_set(x_25, 0, x_38);
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_25);
x_39 = l_Lean_instInhabitedExpr;
x_40 = l_Array_back_x21___redArg(x_39, x_3);
lean_dec_ref(x_3);
lean_inc(x_40);
x_41 = l_Lean_Meta_Grind_getRootENode___redArg(x_40, x_5, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get_uint8(x_43, sizeof(void*)*11 + 2);
x_46 = lean_ctor_get_uint8(x_43, sizeof(void*)*11 + 4);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_91; 
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_91 = lean_box(0);
lean_ctor_set(x_41, 0, x_91);
return x_41;
}
else
{
lean_object* x_92; 
lean_free_object(x_41);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_44);
x_92 = l_Lean_Meta_isConstructorApp_x3f(x_44, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_92, 0);
if (lean_obj_tag(x_94) == 1)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_free_object(x_92);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
if (x_46 == 0)
{
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
x_96 = x_5;
x_97 = x_6;
x_98 = x_7;
x_99 = x_8;
x_100 = x_9;
x_101 = x_10;
x_102 = x_11;
x_103 = x_12;
x_104 = x_13;
x_105 = x_14;
x_106 = lean_box(0);
goto block_136;
}
else
{
lean_object* x_137; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_44);
lean_inc(x_40);
x_137 = l_Lean_Meta_Grind_hasSameType(x_40, x_44, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_95);
lean_dec_ref(x_1);
x_140 = l_Lean_Meta_Grind_getGeneration___redArg(x_40, x_5);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = l_Lean_Meta_Grind_getGeneration___redArg(x_44, x_5);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; uint8_t x_195; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_195 = lean_nat_dec_le(x_141, x_143);
if (x_195 == 0)
{
lean_dec(x_143);
x_144 = x_141;
goto block_194;
}
else
{
lean_dec(x_141);
x_144 = x_143;
goto block_194;
}
block_194:
{
lean_object* x_145; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_40);
x_145 = lean_infer_type(x_40, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec_ref(x_145);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_147 = l_Lean_Meta_whnfD(x_146, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec_ref(x_147);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_44);
x_149 = lean_infer_type(x_44, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec_ref(x_149);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_151 = l_Lean_Meta_whnfD(x_150, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_151) == 0)
{
uint8_t x_152; 
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_153 = lean_ctor_get(x_151, 0);
x_154 = lean_ctor_get(x_30, 0);
lean_inc(x_154);
lean_dec_ref(x_30);
lean_inc(x_34);
x_155 = l_Lean_Expr_isAppOfArity(x_148, x_154, x_34);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_154);
lean_free_object(x_151);
lean_dec(x_153);
lean_dec(x_148);
lean_dec(x_144);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_24);
x_156 = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4);
x_157 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_156, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_157;
}
else
{
uint8_t x_158; 
x_158 = l_Lean_Expr_isAppOfArity(x_153, x_154, x_34);
if (x_158 == 0)
{
lean_object* x_159; 
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_148);
lean_dec(x_144);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_159 = lean_box(0);
lean_ctor_set(x_151, 0, x_159);
return x_151;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
lean_free_object(x_151);
x_160 = lean_st_ref_get(x_14);
x_161 = lean_ctor_get(x_160, 0);
lean_inc_ref(x_161);
lean_dec(x_160);
x_162 = l_Lean_Expr_getAppFn(x_148);
x_163 = l_Lean_Expr_constLevels_x21(x_162);
lean_dec_ref(x_162);
x_164 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_154);
x_165 = l_Lean_Environment_containsOnBranch(x_161, x_164);
if (x_165 == 0)
{
lean_object* x_166; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_164);
x_166 = l_Lean_executeReservedNameAction(x_164, x_13, x_14);
if (lean_obj_tag(x_166) == 0)
{
lean_dec_ref(x_166);
x_47 = x_148;
x_48 = x_163;
x_49 = x_153;
x_50 = x_144;
x_51 = x_164;
x_52 = x_5;
x_53 = x_6;
x_54 = x_7;
x_55 = x_8;
x_56 = x_9;
x_57 = x_10;
x_58 = x_11;
x_59 = x_12;
x_60 = x_13;
x_61 = x_14;
x_62 = lean_box(0);
goto block_90;
}
else
{
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_153);
lean_dec(x_148);
lean_dec(x_144);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_166;
}
}
else
{
x_47 = x_148;
x_48 = x_163;
x_49 = x_153;
x_50 = x_144;
x_51 = x_164;
x_52 = x_5;
x_53 = x_6;
x_54 = x_7;
x_55 = x_8;
x_56 = x_9;
x_57 = x_10;
x_58 = x_11;
x_59 = x_12;
x_60 = x_13;
x_61 = x_14;
x_62 = lean_box(0);
goto block_90;
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_167 = lean_ctor_get(x_151, 0);
lean_inc(x_167);
lean_dec(x_151);
x_168 = lean_ctor_get(x_30, 0);
lean_inc(x_168);
lean_dec_ref(x_30);
lean_inc(x_34);
x_169 = l_Lean_Expr_isAppOfArity(x_148, x_168, x_34);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_148);
lean_dec(x_144);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_24);
x_170 = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4);
x_171 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_170, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_171;
}
else
{
uint8_t x_172; 
x_172 = l_Lean_Expr_isAppOfArity(x_167, x_168, x_34);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_148);
lean_dec(x_144);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_173 = lean_box(0);
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_173);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_175 = lean_st_ref_get(x_14);
x_176 = lean_ctor_get(x_175, 0);
lean_inc_ref(x_176);
lean_dec(x_175);
x_177 = l_Lean_Expr_getAppFn(x_148);
x_178 = l_Lean_Expr_constLevels_x21(x_177);
lean_dec_ref(x_177);
x_179 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_168);
x_180 = l_Lean_Environment_containsOnBranch(x_176, x_179);
if (x_180 == 0)
{
lean_object* x_181; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_179);
x_181 = l_Lean_executeReservedNameAction(x_179, x_13, x_14);
if (lean_obj_tag(x_181) == 0)
{
lean_dec_ref(x_181);
x_47 = x_148;
x_48 = x_178;
x_49 = x_167;
x_50 = x_144;
x_51 = x_179;
x_52 = x_5;
x_53 = x_6;
x_54 = x_7;
x_55 = x_8;
x_56 = x_9;
x_57 = x_10;
x_58 = x_11;
x_59 = x_12;
x_60 = x_13;
x_61 = x_14;
x_62 = lean_box(0);
goto block_90;
}
else
{
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_167);
lean_dec(x_148);
lean_dec(x_144);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_181;
}
}
else
{
x_47 = x_148;
x_48 = x_178;
x_49 = x_167;
x_50 = x_144;
x_51 = x_179;
x_52 = x_5;
x_53 = x_6;
x_54 = x_7;
x_55 = x_8;
x_56 = x_9;
x_57 = x_10;
x_58 = x_11;
x_59 = x_12;
x_60 = x_13;
x_61 = x_14;
x_62 = lean_box(0);
goto block_90;
}
}
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_148);
lean_dec(x_144);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_182 = !lean_is_exclusive(x_151);
if (x_182 == 0)
{
return x_151;
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_151, 0);
lean_inc(x_183);
lean_dec(x_151);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_148);
lean_dec(x_144);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_185 = !lean_is_exclusive(x_149);
if (x_185 == 0)
{
return x_149;
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_149, 0);
lean_inc(x_186);
lean_dec(x_149);
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_144);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_188 = !lean_is_exclusive(x_147);
if (x_188 == 0)
{
return x_147;
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_147, 0);
lean_inc(x_189);
lean_dec(x_147);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_189);
return x_190;
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_144);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_191 = !lean_is_exclusive(x_145);
if (x_191 == 0)
{
return x_145;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_145, 0);
lean_inc(x_192);
lean_dec(x_145);
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_192);
return x_193;
}
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_141);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_196 = !lean_is_exclusive(x_142);
if (x_196 == 0)
{
return x_142;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_142, 0);
lean_inc(x_197);
lean_dec(x_142);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_197);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_199 = !lean_is_exclusive(x_140);
if (x_199 == 0)
{
return x_140;
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_140, 0);
lean_inc(x_200);
lean_dec(x_140);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
}
}
else
{
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
x_96 = x_5;
x_97 = x_6;
x_98 = x_7;
x_99 = x_8;
x_100 = x_9;
x_101 = x_10;
x_102 = x_11;
x_103 = x_12;
x_104 = x_13;
x_105 = x_14;
x_106 = lean_box(0);
goto block_136;
}
}
else
{
uint8_t x_202; 
lean_dec(x_95);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_202 = !lean_is_exclusive(x_137);
if (x_202 == 0)
{
return x_137;
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_137, 0);
lean_inc(x_203);
lean_dec(x_137);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
return x_204;
}
}
}
block_136:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_95, 2);
lean_inc(x_107);
lean_dec(x_95);
x_108 = l_Lean_mkNatLit(x_107);
x_109 = l_Lean_Meta_Sym_shareCommon___redArg(x_108, x_101);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
x_111 = lean_unsigned_to_nat(0u);
x_112 = lean_box(0);
lean_inc(x_105);
lean_inc_ref(x_104);
lean_inc(x_103);
lean_inc_ref(x_102);
lean_inc(x_101);
lean_inc_ref(x_100);
lean_inc(x_99);
lean_inc_ref(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_110);
x_113 = lean_grind_internalize(x_110, x_111, x_112, x_96, x_97, x_98, x_99, x_100, x_101, x_102, x_103, x_104, x_105);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
lean_dec_ref(x_113);
lean_inc(x_105);
lean_inc_ref(x_104);
lean_inc(x_103);
lean_inc_ref(x_102);
lean_inc_ref(x_98);
lean_inc(x_96);
x_114 = lean_grind_mk_eq_proof(x_40, x_44, x_96, x_97, x_98, x_99, x_100, x_101, x_102, x_103, x_104, x_105);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec_ref(x_114);
x_116 = l_Lean_Expr_appFn_x21(x_1);
lean_inc(x_105);
lean_inc_ref(x_104);
lean_inc(x_103);
lean_inc_ref(x_102);
x_117 = l_Lean_Meta_mkCongrArg(x_116, x_115, x_102, x_103, x_104, x_105);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
lean_inc(x_105);
lean_inc_ref(x_104);
lean_inc(x_103);
lean_inc_ref(x_102);
lean_inc(x_110);
lean_inc_ref(x_1);
x_119 = l_Lean_Meta_mkEq(x_1, x_110, x_102, x_103, x_104, x_105);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
x_121 = l_Lean_Meta_mkExpectedPropHint(x_118, x_120);
x_122 = 0;
x_123 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_110, x_121, x_122, x_96, x_98, x_102, x_103, x_104, x_105);
lean_dec_ref(x_98);
lean_dec(x_96);
return x_123;
}
else
{
uint8_t x_124; 
lean_dec(x_118);
lean_dec(x_110);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec_ref(x_98);
lean_dec(x_96);
lean_dec_ref(x_1);
x_124 = !lean_is_exclusive(x_119);
if (x_124 == 0)
{
return x_119;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_119, 0);
lean_inc(x_125);
lean_dec(x_119);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_110);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec_ref(x_98);
lean_dec(x_96);
lean_dec_ref(x_1);
x_127 = !lean_is_exclusive(x_117);
if (x_127 == 0)
{
return x_117;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_117, 0);
lean_inc(x_128);
lean_dec(x_117);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_110);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec_ref(x_98);
lean_dec(x_96);
lean_dec_ref(x_1);
x_130 = !lean_is_exclusive(x_114);
if (x_130 == 0)
{
return x_114;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_114, 0);
lean_inc(x_131);
lean_dec(x_114);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
}
else
{
lean_dec(x_110);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec_ref(x_1);
return x_113;
}
}
else
{
uint8_t x_133; 
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec_ref(x_1);
x_133 = !lean_is_exclusive(x_109);
if (x_133 == 0)
{
return x_109;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_109, 0);
lean_inc(x_134);
lean_dec(x_109);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
}
else
{
lean_object* x_205; 
lean_dec(x_94);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_205 = lean_box(0);
lean_ctor_set(x_92, 0, x_205);
return x_92;
}
}
else
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_92, 0);
lean_inc(x_206);
lean_dec(x_92);
if (lean_obj_tag(x_206) == 1)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
lean_dec_ref(x_206);
if (x_46 == 0)
{
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
x_208 = x_5;
x_209 = x_6;
x_210 = x_7;
x_211 = x_8;
x_212 = x_9;
x_213 = x_10;
x_214 = x_11;
x_215 = x_12;
x_216 = x_13;
x_217 = x_14;
x_218 = lean_box(0);
goto block_248;
}
else
{
lean_object* x_249; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_44);
lean_inc(x_40);
x_249 = l_Lean_Meta_Grind_hasSameType(x_40, x_44, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; uint8_t x_251; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_dec_ref(x_249);
x_251 = lean_unbox(x_250);
lean_dec(x_250);
if (x_251 == 0)
{
lean_object* x_252; 
lean_dec(x_207);
lean_dec_ref(x_1);
x_252 = l_Lean_Meta_Grind_getGeneration___redArg(x_40, x_5);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec_ref(x_252);
x_254 = l_Lean_Meta_Grind_getGeneration___redArg(x_44, x_5);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; uint8_t x_293; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
lean_dec_ref(x_254);
x_293 = lean_nat_dec_le(x_253, x_255);
if (x_293 == 0)
{
lean_dec(x_255);
x_256 = x_253;
goto block_292;
}
else
{
lean_dec(x_253);
x_256 = x_255;
goto block_292;
}
block_292:
{
lean_object* x_257; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_40);
x_257 = lean_infer_type(x_40, x_11, x_12, x_13, x_14);
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
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
lean_dec_ref(x_259);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_44);
x_261 = lean_infer_type(x_44, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
lean_dec_ref(x_261);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_263 = l_Lean_Meta_whnfD(x_262, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 x_265 = x_263;
} else {
 lean_dec_ref(x_263);
 x_265 = lean_box(0);
}
x_266 = lean_ctor_get(x_30, 0);
lean_inc(x_266);
lean_dec_ref(x_30);
lean_inc(x_34);
x_267 = l_Lean_Expr_isAppOfArity(x_260, x_266, x_34);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; 
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_260);
lean_dec(x_256);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_24);
x_268 = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4);
x_269 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_268, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_269;
}
else
{
uint8_t x_270; 
x_270 = l_Lean_Expr_isAppOfArity(x_264, x_266, x_34);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; 
lean_dec(x_266);
lean_dec(x_264);
lean_dec(x_260);
lean_dec(x_256);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_271 = lean_box(0);
if (lean_is_scalar(x_265)) {
 x_272 = lean_alloc_ctor(0, 1, 0);
} else {
 x_272 = x_265;
}
lean_ctor_set(x_272, 0, x_271);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
lean_dec(x_265);
x_273 = lean_st_ref_get(x_14);
x_274 = lean_ctor_get(x_273, 0);
lean_inc_ref(x_274);
lean_dec(x_273);
x_275 = l_Lean_Expr_getAppFn(x_260);
x_276 = l_Lean_Expr_constLevels_x21(x_275);
lean_dec_ref(x_275);
x_277 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_266);
x_278 = l_Lean_Environment_containsOnBranch(x_274, x_277);
if (x_278 == 0)
{
lean_object* x_279; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_277);
x_279 = l_Lean_executeReservedNameAction(x_277, x_13, x_14);
if (lean_obj_tag(x_279) == 0)
{
lean_dec_ref(x_279);
x_47 = x_260;
x_48 = x_276;
x_49 = x_264;
x_50 = x_256;
x_51 = x_277;
x_52 = x_5;
x_53 = x_6;
x_54 = x_7;
x_55 = x_8;
x_56 = x_9;
x_57 = x_10;
x_58 = x_11;
x_59 = x_12;
x_60 = x_13;
x_61 = x_14;
x_62 = lean_box(0);
goto block_90;
}
else
{
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_264);
lean_dec(x_260);
lean_dec(x_256);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_279;
}
}
else
{
x_47 = x_260;
x_48 = x_276;
x_49 = x_264;
x_50 = x_256;
x_51 = x_277;
x_52 = x_5;
x_53 = x_6;
x_54 = x_7;
x_55 = x_8;
x_56 = x_9;
x_57 = x_10;
x_58 = x_11;
x_59 = x_12;
x_60 = x_13;
x_61 = x_14;
x_62 = lean_box(0);
goto block_90;
}
}
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_260);
lean_dec(x_256);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_280 = lean_ctor_get(x_263, 0);
lean_inc(x_280);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 x_281 = x_263;
} else {
 lean_dec_ref(x_263);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 1, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_280);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_260);
lean_dec(x_256);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_283 = lean_ctor_get(x_261, 0);
lean_inc(x_283);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 x_284 = x_261;
} else {
 lean_dec_ref(x_261);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(1, 1, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_283);
return x_285;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_256);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_286 = lean_ctor_get(x_259, 0);
lean_inc(x_286);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 x_287 = x_259;
} else {
 lean_dec_ref(x_259);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 1, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_286);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_256);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_289 = lean_ctor_get(x_257, 0);
lean_inc(x_289);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_290 = x_257;
} else {
 lean_dec_ref(x_257);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(1, 1, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_289);
return x_291;
}
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_253);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_294 = lean_ctor_get(x_254, 0);
lean_inc(x_294);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 x_295 = x_254;
} else {
 lean_dec_ref(x_254);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 1, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_294);
return x_296;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_297 = lean_ctor_get(x_252, 0);
lean_inc(x_297);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 x_298 = x_252;
} else {
 lean_dec_ref(x_252);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 1, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_297);
return x_299;
}
}
else
{
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
x_208 = x_5;
x_209 = x_6;
x_210 = x_7;
x_211 = x_8;
x_212 = x_9;
x_213 = x_10;
x_214 = x_11;
x_215 = x_12;
x_216 = x_13;
x_217 = x_14;
x_218 = lean_box(0);
goto block_248;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_207);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_300 = lean_ctor_get(x_249, 0);
lean_inc(x_300);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 x_301 = x_249;
} else {
 lean_dec_ref(x_249);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 1, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_300);
return x_302;
}
}
block_248:
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_207, 2);
lean_inc(x_219);
lean_dec(x_207);
x_220 = l_Lean_mkNatLit(x_219);
x_221 = l_Lean_Meta_Sym_shareCommon___redArg(x_220, x_213);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_dec_ref(x_221);
x_223 = lean_unsigned_to_nat(0u);
x_224 = lean_box(0);
lean_inc(x_217);
lean_inc_ref(x_216);
lean_inc(x_215);
lean_inc_ref(x_214);
lean_inc(x_213);
lean_inc_ref(x_212);
lean_inc(x_211);
lean_inc_ref(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_222);
x_225 = lean_grind_internalize(x_222, x_223, x_224, x_208, x_209, x_210, x_211, x_212, x_213, x_214, x_215, x_216, x_217);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; 
lean_dec_ref(x_225);
lean_inc(x_217);
lean_inc_ref(x_216);
lean_inc(x_215);
lean_inc_ref(x_214);
lean_inc_ref(x_210);
lean_inc(x_208);
x_226 = lean_grind_mk_eq_proof(x_40, x_44, x_208, x_209, x_210, x_211, x_212, x_213, x_214, x_215, x_216, x_217);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec_ref(x_226);
x_228 = l_Lean_Expr_appFn_x21(x_1);
lean_inc(x_217);
lean_inc_ref(x_216);
lean_inc(x_215);
lean_inc_ref(x_214);
x_229 = l_Lean_Meta_mkCongrArg(x_228, x_227, x_214, x_215, x_216, x_217);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
lean_dec_ref(x_229);
lean_inc(x_217);
lean_inc_ref(x_216);
lean_inc(x_215);
lean_inc_ref(x_214);
lean_inc(x_222);
lean_inc_ref(x_1);
x_231 = l_Lean_Meta_mkEq(x_1, x_222, x_214, x_215, x_216, x_217);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
lean_dec_ref(x_231);
x_233 = l_Lean_Meta_mkExpectedPropHint(x_230, x_232);
x_234 = 0;
x_235 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_222, x_233, x_234, x_208, x_210, x_214, x_215, x_216, x_217);
lean_dec_ref(x_210);
lean_dec(x_208);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_230);
lean_dec(x_222);
lean_dec(x_217);
lean_dec_ref(x_216);
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec_ref(x_210);
lean_dec(x_208);
lean_dec_ref(x_1);
x_236 = lean_ctor_get(x_231, 0);
lean_inc(x_236);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_237 = x_231;
} else {
 lean_dec_ref(x_231);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(1, 1, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_236);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_222);
lean_dec(x_217);
lean_dec_ref(x_216);
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec_ref(x_210);
lean_dec(x_208);
lean_dec_ref(x_1);
x_239 = lean_ctor_get(x_229, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 x_240 = x_229;
} else {
 lean_dec_ref(x_229);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 1, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_239);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_222);
lean_dec(x_217);
lean_dec_ref(x_216);
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec_ref(x_210);
lean_dec(x_208);
lean_dec_ref(x_1);
x_242 = lean_ctor_get(x_226, 0);
lean_inc(x_242);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 x_243 = x_226;
} else {
 lean_dec_ref(x_226);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 1, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_242);
return x_244;
}
}
else
{
lean_dec(x_222);
lean_dec(x_217);
lean_dec_ref(x_216);
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec_ref(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec_ref(x_1);
return x_225;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_217);
lean_dec_ref(x_216);
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec(x_211);
lean_dec_ref(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec_ref(x_1);
x_245 = lean_ctor_get(x_221, 0);
lean_inc(x_245);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 x_246 = x_221;
} else {
 lean_dec_ref(x_221);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 1, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_245);
return x_247;
}
}
}
else
{
lean_object* x_303; lean_object* x_304; 
lean_dec(x_206);
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_303 = lean_box(0);
x_304 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_304, 0, x_303);
return x_304;
}
}
}
else
{
uint8_t x_305; 
lean_dec_ref(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_305 = !lean_is_exclusive(x_92);
if (x_305 == 0)
{
return x_92;
}
else
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_ctor_get(x_92, 0);
lean_inc(x_306);
lean_dec(x_92);
x_307 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_307, 0, x_306);
return x_307;
}
}
}
block_90:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_inc(x_51);
x_63 = l_Lean_mkConst(x_51, x_48);
x_64 = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
x_65 = l_Lean_Expr_getAppNumArgs(x_47);
lean_inc(x_65);
x_66 = lean_mk_array(x_65, x_64);
x_67 = lean_nat_sub(x_65, x_35);
lean_dec(x_65);
x_68 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_47, x_66, x_67);
x_69 = l_Lean_mkAppN(x_63, x_68);
lean_dec_ref(x_68);
x_70 = l_Lean_Expr_app___override(x_69, x_40);
x_71 = l_Lean_Expr_getAppNumArgs(x_49);
lean_inc(x_71);
x_72 = lean_mk_array(x_71, x_64);
x_73 = lean_nat_sub(x_71, x_35);
lean_dec(x_71);
x_74 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_49, x_72, x_73);
x_75 = l_Lean_mkAppN(x_70, x_74);
lean_dec_ref(x_74);
x_76 = l_Lean_Expr_app___override(x_75, x_44);
lean_inc(x_61);
lean_inc_ref(x_60);
lean_inc(x_59);
lean_inc_ref(x_58);
lean_inc_ref(x_76);
x_77 = lean_infer_type(x_76, x_58, x_59, x_60, x_61);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
if (lean_is_scalar(x_29)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_29;
 lean_ctor_set_tag(x_79, 0);
}
lean_ctor_set(x_79, 0, x_51);
if (lean_is_scalar(x_24)) {
 x_80 = lean_alloc_ctor(7, 1, 0);
} else {
 x_80 = x_24;
 lean_ctor_set_tag(x_80, 7);
}
lean_ctor_set(x_80, 0, x_79);
x_81 = l_Lean_Meta_Grind_addNewRawFact(x_76, x_78, x_50, x_80, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61);
lean_dec(x_57);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec(x_52);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
x_84 = lean_box(0);
lean_ctor_set(x_81, 0, x_84);
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_81);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
else
{
return x_81;
}
}
else
{
uint8_t x_87; 
lean_dec_ref(x_76);
lean_dec(x_61);
lean_dec_ref(x_60);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_29);
lean_dec(x_24);
x_87 = !lean_is_exclusive(x_77);
if (x_87 == 0)
{
return x_77;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_77, 0);
lean_inc(x_88);
lean_dec(x_77);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
}
else
{
lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_308 = lean_ctor_get(x_41, 0);
lean_inc(x_308);
lean_dec(x_41);
x_309 = lean_ctor_get(x_308, 0);
lean_inc_ref(x_309);
x_310 = lean_ctor_get_uint8(x_308, sizeof(void*)*11 + 2);
x_311 = lean_ctor_get_uint8(x_308, sizeof(void*)*11 + 4);
lean_dec(x_308);
if (x_310 == 0)
{
lean_object* x_354; lean_object* x_355; 
lean_dec_ref(x_309);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_354 = lean_box(0);
x_355 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_355, 0, x_354);
return x_355;
}
else
{
lean_object* x_356; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_309);
x_356 = l_Lean_Meta_isConstructorApp_x3f(x_309, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; 
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 x_358 = x_356;
} else {
 lean_dec_ref(x_356);
 x_358 = lean_box(0);
}
if (lean_obj_tag(x_357) == 1)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_358);
x_359 = lean_ctor_get(x_357, 0);
lean_inc(x_359);
lean_dec_ref(x_357);
if (x_311 == 0)
{
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
x_360 = x_5;
x_361 = x_6;
x_362 = x_7;
x_363 = x_8;
x_364 = x_9;
x_365 = x_10;
x_366 = x_11;
x_367 = x_12;
x_368 = x_13;
x_369 = x_14;
x_370 = lean_box(0);
goto block_400;
}
else
{
lean_object* x_401; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_309);
lean_inc(x_40);
x_401 = l_Lean_Meta_Grind_hasSameType(x_40, x_309, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; uint8_t x_403; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
lean_dec_ref(x_401);
x_403 = lean_unbox(x_402);
lean_dec(x_402);
if (x_403 == 0)
{
lean_object* x_404; 
lean_dec(x_359);
lean_dec_ref(x_1);
x_404 = l_Lean_Meta_Grind_getGeneration___redArg(x_40, x_5);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
lean_dec_ref(x_404);
x_406 = l_Lean_Meta_Grind_getGeneration___redArg(x_309, x_5);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; uint8_t x_445; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
lean_dec_ref(x_406);
x_445 = lean_nat_dec_le(x_405, x_407);
if (x_445 == 0)
{
lean_dec(x_407);
x_408 = x_405;
goto block_444;
}
else
{
lean_dec(x_405);
x_408 = x_407;
goto block_444;
}
block_444:
{
lean_object* x_409; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_40);
x_409 = lean_infer_type(x_40, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
lean_dec_ref(x_409);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_411 = l_Lean_Meta_whnfD(x_410, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
lean_dec_ref(x_411);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_309);
x_413 = lean_infer_type(x_309, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; 
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
lean_dec_ref(x_413);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_415 = l_Lean_Meta_whnfD(x_414, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; 
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 x_417 = x_415;
} else {
 lean_dec_ref(x_415);
 x_417 = lean_box(0);
}
x_418 = lean_ctor_get(x_30, 0);
lean_inc(x_418);
lean_dec_ref(x_30);
lean_inc(x_34);
x_419 = l_Lean_Expr_isAppOfArity(x_412, x_418, x_34);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; 
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_412);
lean_dec(x_408);
lean_dec_ref(x_309);
lean_dec(x_40);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_24);
x_420 = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4);
x_421 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_420, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_421;
}
else
{
uint8_t x_422; 
x_422 = l_Lean_Expr_isAppOfArity(x_416, x_418, x_34);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; 
lean_dec(x_418);
lean_dec(x_416);
lean_dec(x_412);
lean_dec(x_408);
lean_dec_ref(x_309);
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_423 = lean_box(0);
if (lean_is_scalar(x_417)) {
 x_424 = lean_alloc_ctor(0, 1, 0);
} else {
 x_424 = x_417;
}
lean_ctor_set(x_424, 0, x_423);
return x_424;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; uint8_t x_430; 
lean_dec(x_417);
x_425 = lean_st_ref_get(x_14);
x_426 = lean_ctor_get(x_425, 0);
lean_inc_ref(x_426);
lean_dec(x_425);
x_427 = l_Lean_Expr_getAppFn(x_412);
x_428 = l_Lean_Expr_constLevels_x21(x_427);
lean_dec_ref(x_427);
x_429 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_418);
x_430 = l_Lean_Environment_containsOnBranch(x_426, x_429);
if (x_430 == 0)
{
lean_object* x_431; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_429);
x_431 = l_Lean_executeReservedNameAction(x_429, x_13, x_14);
if (lean_obj_tag(x_431) == 0)
{
lean_dec_ref(x_431);
x_312 = x_412;
x_313 = x_428;
x_314 = x_416;
x_315 = x_408;
x_316 = x_429;
x_317 = x_5;
x_318 = x_6;
x_319 = x_7;
x_320 = x_8;
x_321 = x_9;
x_322 = x_10;
x_323 = x_11;
x_324 = x_12;
x_325 = x_13;
x_326 = x_14;
x_327 = lean_box(0);
goto block_353;
}
else
{
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_416);
lean_dec(x_412);
lean_dec(x_408);
lean_dec_ref(x_309);
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_431;
}
}
else
{
x_312 = x_412;
x_313 = x_428;
x_314 = x_416;
x_315 = x_408;
x_316 = x_429;
x_317 = x_5;
x_318 = x_6;
x_319 = x_7;
x_320 = x_8;
x_321 = x_9;
x_322 = x_10;
x_323 = x_11;
x_324 = x_12;
x_325 = x_13;
x_326 = x_14;
x_327 = lean_box(0);
goto block_353;
}
}
}
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
lean_dec(x_412);
lean_dec(x_408);
lean_dec_ref(x_309);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_432 = lean_ctor_get(x_415, 0);
lean_inc(x_432);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 x_433 = x_415;
} else {
 lean_dec_ref(x_415);
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
lean_dec(x_412);
lean_dec(x_408);
lean_dec_ref(x_309);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_435 = lean_ctor_get(x_413, 0);
lean_inc(x_435);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 x_436 = x_413;
} else {
 lean_dec_ref(x_413);
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
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_dec(x_408);
lean_dec_ref(x_309);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_438 = lean_ctor_get(x_411, 0);
lean_inc(x_438);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 x_439 = x_411;
} else {
 lean_dec_ref(x_411);
 x_439 = lean_box(0);
}
if (lean_is_scalar(x_439)) {
 x_440 = lean_alloc_ctor(1, 1, 0);
} else {
 x_440 = x_439;
}
lean_ctor_set(x_440, 0, x_438);
return x_440;
}
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_408);
lean_dec_ref(x_309);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_441 = lean_ctor_get(x_409, 0);
lean_inc(x_441);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 x_442 = x_409;
} else {
 lean_dec_ref(x_409);
 x_442 = lean_box(0);
}
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 1, 0);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_441);
return x_443;
}
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_405);
lean_dec_ref(x_309);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_446 = lean_ctor_get(x_406, 0);
lean_inc(x_446);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 x_447 = x_406;
} else {
 lean_dec_ref(x_406);
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
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec_ref(x_309);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_449 = lean_ctor_get(x_404, 0);
lean_inc(x_449);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 x_450 = x_404;
} else {
 lean_dec_ref(x_404);
 x_450 = lean_box(0);
}
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(1, 1, 0);
} else {
 x_451 = x_450;
}
lean_ctor_set(x_451, 0, x_449);
return x_451;
}
}
else
{
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
x_360 = x_5;
x_361 = x_6;
x_362 = x_7;
x_363 = x_8;
x_364 = x_9;
x_365 = x_10;
x_366 = x_11;
x_367 = x_12;
x_368 = x_13;
x_369 = x_14;
x_370 = lean_box(0);
goto block_400;
}
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_359);
lean_dec_ref(x_309);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_452 = lean_ctor_get(x_401, 0);
lean_inc(x_452);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 x_453 = x_401;
} else {
 lean_dec_ref(x_401);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 1, 0);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_452);
return x_454;
}
}
block_400:
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_359, 2);
lean_inc(x_371);
lean_dec(x_359);
x_372 = l_Lean_mkNatLit(x_371);
x_373 = l_Lean_Meta_Sym_shareCommon___redArg(x_372, x_365);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
lean_dec_ref(x_373);
x_375 = lean_unsigned_to_nat(0u);
x_376 = lean_box(0);
lean_inc(x_369);
lean_inc_ref(x_368);
lean_inc(x_367);
lean_inc_ref(x_366);
lean_inc(x_365);
lean_inc_ref(x_364);
lean_inc(x_363);
lean_inc_ref(x_362);
lean_inc(x_361);
lean_inc(x_360);
lean_inc(x_374);
x_377 = lean_grind_internalize(x_374, x_375, x_376, x_360, x_361, x_362, x_363, x_364, x_365, x_366, x_367, x_368, x_369);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; 
lean_dec_ref(x_377);
lean_inc(x_369);
lean_inc_ref(x_368);
lean_inc(x_367);
lean_inc_ref(x_366);
lean_inc_ref(x_362);
lean_inc(x_360);
x_378 = lean_grind_mk_eq_proof(x_40, x_309, x_360, x_361, x_362, x_363, x_364, x_365, x_366, x_367, x_368, x_369);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
lean_dec_ref(x_378);
x_380 = l_Lean_Expr_appFn_x21(x_1);
lean_inc(x_369);
lean_inc_ref(x_368);
lean_inc(x_367);
lean_inc_ref(x_366);
x_381 = l_Lean_Meta_mkCongrArg(x_380, x_379, x_366, x_367, x_368, x_369);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
lean_dec_ref(x_381);
lean_inc(x_369);
lean_inc_ref(x_368);
lean_inc(x_367);
lean_inc_ref(x_366);
lean_inc(x_374);
lean_inc_ref(x_1);
x_383 = l_Lean_Meta_mkEq(x_1, x_374, x_366, x_367, x_368, x_369);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; uint8_t x_386; lean_object* x_387; 
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
lean_dec_ref(x_383);
x_385 = l_Lean_Meta_mkExpectedPropHint(x_382, x_384);
x_386 = 0;
x_387 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_374, x_385, x_386, x_360, x_362, x_366, x_367, x_368, x_369);
lean_dec_ref(x_362);
lean_dec(x_360);
return x_387;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_382);
lean_dec(x_374);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec_ref(x_366);
lean_dec_ref(x_362);
lean_dec(x_360);
lean_dec_ref(x_1);
x_388 = lean_ctor_get(x_383, 0);
lean_inc(x_388);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 x_389 = x_383;
} else {
 lean_dec_ref(x_383);
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
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_374);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec_ref(x_366);
lean_dec_ref(x_362);
lean_dec(x_360);
lean_dec_ref(x_1);
x_391 = lean_ctor_get(x_381, 0);
lean_inc(x_391);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 x_392 = x_381;
} else {
 lean_dec_ref(x_381);
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
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_374);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec_ref(x_366);
lean_dec_ref(x_362);
lean_dec(x_360);
lean_dec_ref(x_1);
x_394 = lean_ctor_get(x_378, 0);
lean_inc(x_394);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 x_395 = x_378;
} else {
 lean_dec_ref(x_378);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 1, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_394);
return x_396;
}
}
else
{
lean_dec(x_374);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec_ref(x_366);
lean_dec(x_365);
lean_dec_ref(x_364);
lean_dec(x_363);
lean_dec_ref(x_362);
lean_dec(x_361);
lean_dec(x_360);
lean_dec_ref(x_309);
lean_dec(x_40);
lean_dec_ref(x_1);
return x_377;
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec_ref(x_366);
lean_dec(x_365);
lean_dec_ref(x_364);
lean_dec(x_363);
lean_dec_ref(x_362);
lean_dec(x_361);
lean_dec(x_360);
lean_dec_ref(x_309);
lean_dec(x_40);
lean_dec_ref(x_1);
x_397 = lean_ctor_get(x_373, 0);
lean_inc(x_397);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 x_398 = x_373;
} else {
 lean_dec_ref(x_373);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 1, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_397);
return x_399;
}
}
}
else
{
lean_object* x_455; lean_object* x_456; 
lean_dec(x_357);
lean_dec_ref(x_309);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_455 = lean_box(0);
if (lean_is_scalar(x_358)) {
 x_456 = lean_alloc_ctor(0, 1, 0);
} else {
 x_456 = x_358;
}
lean_ctor_set(x_456, 0, x_455);
return x_456;
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec_ref(x_309);
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_457 = lean_ctor_get(x_356, 0);
lean_inc(x_457);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 x_458 = x_356;
} else {
 lean_dec_ref(x_356);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(1, 1, 0);
} else {
 x_459 = x_458;
}
lean_ctor_set(x_459, 0, x_457);
return x_459;
}
}
block_353:
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_inc(x_316);
x_328 = l_Lean_mkConst(x_316, x_313);
x_329 = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
x_330 = l_Lean_Expr_getAppNumArgs(x_312);
lean_inc(x_330);
x_331 = lean_mk_array(x_330, x_329);
x_332 = lean_nat_sub(x_330, x_35);
lean_dec(x_330);
x_333 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_312, x_331, x_332);
x_334 = l_Lean_mkAppN(x_328, x_333);
lean_dec_ref(x_333);
x_335 = l_Lean_Expr_app___override(x_334, x_40);
x_336 = l_Lean_Expr_getAppNumArgs(x_314);
lean_inc(x_336);
x_337 = lean_mk_array(x_336, x_329);
x_338 = lean_nat_sub(x_336, x_35);
lean_dec(x_336);
x_339 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_314, x_337, x_338);
x_340 = l_Lean_mkAppN(x_335, x_339);
lean_dec_ref(x_339);
x_341 = l_Lean_Expr_app___override(x_340, x_309);
lean_inc(x_326);
lean_inc_ref(x_325);
lean_inc(x_324);
lean_inc_ref(x_323);
lean_inc_ref(x_341);
x_342 = lean_infer_type(x_341, x_323, x_324, x_325, x_326);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
lean_dec_ref(x_342);
if (lean_is_scalar(x_29)) {
 x_344 = lean_alloc_ctor(0, 1, 0);
} else {
 x_344 = x_29;
 lean_ctor_set_tag(x_344, 0);
}
lean_ctor_set(x_344, 0, x_316);
if (lean_is_scalar(x_24)) {
 x_345 = lean_alloc_ctor(7, 1, 0);
} else {
 x_345 = x_24;
 lean_ctor_set_tag(x_345, 7);
}
lean_ctor_set(x_345, 0, x_344);
x_346 = l_Lean_Meta_Grind_addNewRawFact(x_341, x_343, x_315, x_345, x_317, x_318, x_319, x_320, x_321, x_322, x_323, x_324, x_325, x_326);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec_ref(x_319);
lean_dec(x_318);
lean_dec(x_317);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 x_347 = x_346;
} else {
 lean_dec_ref(x_346);
 x_347 = lean_box(0);
}
x_348 = lean_box(0);
if (lean_is_scalar(x_347)) {
 x_349 = lean_alloc_ctor(0, 1, 0);
} else {
 x_349 = x_347;
}
lean_ctor_set(x_349, 0, x_348);
return x_349;
}
else
{
return x_346;
}
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec_ref(x_341);
lean_dec(x_326);
lean_dec_ref(x_325);
lean_dec(x_324);
lean_dec_ref(x_323);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec_ref(x_319);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_29);
lean_dec(x_24);
x_350 = lean_ctor_get(x_342, 0);
lean_inc(x_350);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 x_351 = x_342;
} else {
 lean_dec_ref(x_342);
 x_351 = lean_box(0);
}
if (lean_is_scalar(x_351)) {
 x_352 = lean_alloc_ctor(1, 1, 0);
} else {
 x_352 = x_351;
}
lean_ctor_set(x_352, 0, x_350);
return x_352;
}
}
}
}
else
{
uint8_t x_460; 
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_460 = !lean_is_exclusive(x_41);
if (x_460 == 0)
{
return x_41;
}
else
{
lean_object* x_461; lean_object* x_462; 
x_461 = lean_ctor_get(x_41, 0);
lean_inc(x_461);
lean_dec(x_41);
x_462 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_462, 0, x_461);
return x_462;
}
}
}
}
else
{
lean_object* x_463; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_463 = lean_box(0);
lean_ctor_set(x_25, 0, x_463);
return x_25;
}
}
else
{
lean_object* x_464; 
x_464 = lean_ctor_get(x_25, 0);
lean_inc(x_464);
lean_dec(x_25);
if (lean_obj_tag(x_464) == 1)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; uint8_t x_474; 
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 x_466 = x_464;
} else {
 lean_dec_ref(x_464);
 x_466 = lean_box(0);
}
x_467 = lean_ctor_get(x_465, 0);
lean_inc_ref(x_467);
x_468 = lean_ctor_get(x_465, 1);
lean_inc(x_468);
x_469 = lean_ctor_get(x_465, 2);
lean_inc(x_469);
lean_dec(x_465);
x_470 = lean_array_get_size(x_3);
x_471 = lean_nat_add(x_468, x_469);
lean_dec(x_469);
lean_dec(x_468);
x_472 = lean_unsigned_to_nat(1u);
x_473 = lean_nat_add(x_471, x_472);
x_474 = lean_nat_dec_eq(x_470, x_473);
lean_dec(x_473);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; 
lean_dec(x_471);
lean_dec_ref(x_467);
lean_dec(x_466);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_475 = lean_box(0);
x_476 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_476, 0, x_475);
return x_476;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = l_Lean_instInhabitedExpr;
x_478 = l_Array_back_x21___redArg(x_477, x_3);
lean_dec_ref(x_3);
lean_inc(x_478);
x_479 = l_Lean_Meta_Grind_getRootENode___redArg(x_478, x_5, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; uint8_t x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 x_481 = x_479;
} else {
 lean_dec_ref(x_479);
 x_481 = lean_box(0);
}
x_482 = lean_ctor_get(x_480, 0);
lean_inc_ref(x_482);
x_483 = lean_ctor_get_uint8(x_480, sizeof(void*)*11 + 2);
x_484 = lean_ctor_get_uint8(x_480, sizeof(void*)*11 + 4);
lean_dec(x_480);
if (x_483 == 0)
{
lean_object* x_527; lean_object* x_528; 
lean_dec_ref(x_482);
lean_dec(x_478);
lean_dec(x_471);
lean_dec_ref(x_467);
lean_dec(x_466);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_527 = lean_box(0);
if (lean_is_scalar(x_481)) {
 x_528 = lean_alloc_ctor(0, 1, 0);
} else {
 x_528 = x_481;
}
lean_ctor_set(x_528, 0, x_527);
return x_528;
}
else
{
lean_object* x_529; 
lean_dec(x_481);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_482);
x_529 = l_Lean_Meta_isConstructorApp_x3f(x_482, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_530; lean_object* x_531; 
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 x_531 = x_529;
} else {
 lean_dec_ref(x_529);
 x_531 = lean_box(0);
}
if (lean_obj_tag(x_530) == 1)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_531);
x_532 = lean_ctor_get(x_530, 0);
lean_inc(x_532);
lean_dec_ref(x_530);
if (x_484 == 0)
{
lean_dec(x_471);
lean_dec_ref(x_467);
lean_dec(x_466);
lean_dec(x_24);
x_533 = x_5;
x_534 = x_6;
x_535 = x_7;
x_536 = x_8;
x_537 = x_9;
x_538 = x_10;
x_539 = x_11;
x_540 = x_12;
x_541 = x_13;
x_542 = x_14;
x_543 = lean_box(0);
goto block_573;
}
else
{
lean_object* x_574; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_482);
lean_inc(x_478);
x_574 = l_Lean_Meta_Grind_hasSameType(x_478, x_482, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; uint8_t x_576; 
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
lean_dec_ref(x_574);
x_576 = lean_unbox(x_575);
lean_dec(x_575);
if (x_576 == 0)
{
lean_object* x_577; 
lean_dec(x_532);
lean_dec_ref(x_1);
x_577 = l_Lean_Meta_Grind_getGeneration___redArg(x_478, x_5);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; 
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
lean_dec_ref(x_577);
x_579 = l_Lean_Meta_Grind_getGeneration___redArg(x_482, x_5);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; uint8_t x_618; 
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
lean_dec_ref(x_579);
x_618 = lean_nat_dec_le(x_578, x_580);
if (x_618 == 0)
{
lean_dec(x_580);
x_581 = x_578;
goto block_617;
}
else
{
lean_dec(x_578);
x_581 = x_580;
goto block_617;
}
block_617:
{
lean_object* x_582; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_478);
x_582 = lean_infer_type(x_478, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_583; lean_object* x_584; 
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
lean_dec_ref(x_582);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_584 = l_Lean_Meta_whnfD(x_583, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_584) == 0)
{
lean_object* x_585; lean_object* x_586; 
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
lean_dec_ref(x_584);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_482);
x_586 = lean_infer_type(x_482, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; 
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
lean_dec_ref(x_586);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_588 = l_Lean_Meta_whnfD(x_587, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; uint8_t x_592; 
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 x_590 = x_588;
} else {
 lean_dec_ref(x_588);
 x_590 = lean_box(0);
}
x_591 = lean_ctor_get(x_467, 0);
lean_inc(x_591);
lean_dec_ref(x_467);
lean_inc(x_471);
x_592 = l_Lean_Expr_isAppOfArity(x_585, x_591, x_471);
if (x_592 == 0)
{
lean_object* x_593; lean_object* x_594; 
lean_dec(x_591);
lean_dec(x_590);
lean_dec(x_589);
lean_dec(x_585);
lean_dec(x_581);
lean_dec_ref(x_482);
lean_dec(x_478);
lean_dec(x_471);
lean_dec(x_466);
lean_dec(x_24);
x_593 = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4);
x_594 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_593, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_594;
}
else
{
uint8_t x_595; 
x_595 = l_Lean_Expr_isAppOfArity(x_589, x_591, x_471);
if (x_595 == 0)
{
lean_object* x_596; lean_object* x_597; 
lean_dec(x_591);
lean_dec(x_589);
lean_dec(x_585);
lean_dec(x_581);
lean_dec_ref(x_482);
lean_dec(x_478);
lean_dec(x_466);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_596 = lean_box(0);
if (lean_is_scalar(x_590)) {
 x_597 = lean_alloc_ctor(0, 1, 0);
} else {
 x_597 = x_590;
}
lean_ctor_set(x_597, 0, x_596);
return x_597;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; uint8_t x_603; 
lean_dec(x_590);
x_598 = lean_st_ref_get(x_14);
x_599 = lean_ctor_get(x_598, 0);
lean_inc_ref(x_599);
lean_dec(x_598);
x_600 = l_Lean_Expr_getAppFn(x_585);
x_601 = l_Lean_Expr_constLevels_x21(x_600);
lean_dec_ref(x_600);
x_602 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_591);
x_603 = l_Lean_Environment_containsOnBranch(x_599, x_602);
if (x_603 == 0)
{
lean_object* x_604; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_602);
x_604 = l_Lean_executeReservedNameAction(x_602, x_13, x_14);
if (lean_obj_tag(x_604) == 0)
{
lean_dec_ref(x_604);
x_485 = x_585;
x_486 = x_601;
x_487 = x_589;
x_488 = x_581;
x_489 = x_602;
x_490 = x_5;
x_491 = x_6;
x_492 = x_7;
x_493 = x_8;
x_494 = x_9;
x_495 = x_10;
x_496 = x_11;
x_497 = x_12;
x_498 = x_13;
x_499 = x_14;
x_500 = lean_box(0);
goto block_526;
}
else
{
lean_dec(x_602);
lean_dec(x_601);
lean_dec(x_589);
lean_dec(x_585);
lean_dec(x_581);
lean_dec_ref(x_482);
lean_dec(x_478);
lean_dec(x_466);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_604;
}
}
else
{
x_485 = x_585;
x_486 = x_601;
x_487 = x_589;
x_488 = x_581;
x_489 = x_602;
x_490 = x_5;
x_491 = x_6;
x_492 = x_7;
x_493 = x_8;
x_494 = x_9;
x_495 = x_10;
x_496 = x_11;
x_497 = x_12;
x_498 = x_13;
x_499 = x_14;
x_500 = lean_box(0);
goto block_526;
}
}
}
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; 
lean_dec(x_585);
lean_dec(x_581);
lean_dec_ref(x_482);
lean_dec(x_478);
lean_dec(x_471);
lean_dec_ref(x_467);
lean_dec(x_466);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_605 = lean_ctor_get(x_588, 0);
lean_inc(x_605);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 x_606 = x_588;
} else {
 lean_dec_ref(x_588);
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
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_585);
lean_dec(x_581);
lean_dec_ref(x_482);
lean_dec(x_478);
lean_dec(x_471);
lean_dec_ref(x_467);
lean_dec(x_466);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_608 = lean_ctor_get(x_586, 0);
lean_inc(x_608);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 x_609 = x_586;
} else {
 lean_dec_ref(x_586);
 x_609 = lean_box(0);
}
if (lean_is_scalar(x_609)) {
 x_610 = lean_alloc_ctor(1, 1, 0);
} else {
 x_610 = x_609;
}
lean_ctor_set(x_610, 0, x_608);
return x_610;
}
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_581);
lean_dec_ref(x_482);
lean_dec(x_478);
lean_dec(x_471);
lean_dec_ref(x_467);
lean_dec(x_466);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_611 = lean_ctor_get(x_584, 0);
lean_inc(x_611);
if (lean_is_exclusive(x_584)) {
 lean_ctor_release(x_584, 0);
 x_612 = x_584;
} else {
 lean_dec_ref(x_584);
 x_612 = lean_box(0);
}
if (lean_is_scalar(x_612)) {
 x_613 = lean_alloc_ctor(1, 1, 0);
} else {
 x_613 = x_612;
}
lean_ctor_set(x_613, 0, x_611);
return x_613;
}
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
lean_dec(x_581);
lean_dec_ref(x_482);
lean_dec(x_478);
lean_dec(x_471);
lean_dec_ref(x_467);
lean_dec(x_466);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_614 = lean_ctor_get(x_582, 0);
lean_inc(x_614);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 x_615 = x_582;
} else {
 lean_dec_ref(x_582);
 x_615 = lean_box(0);
}
if (lean_is_scalar(x_615)) {
 x_616 = lean_alloc_ctor(1, 1, 0);
} else {
 x_616 = x_615;
}
lean_ctor_set(x_616, 0, x_614);
return x_616;
}
}
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_578);
lean_dec_ref(x_482);
lean_dec(x_478);
lean_dec(x_471);
lean_dec_ref(x_467);
lean_dec(x_466);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_619 = lean_ctor_get(x_579, 0);
lean_inc(x_619);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 x_620 = x_579;
} else {
 lean_dec_ref(x_579);
 x_620 = lean_box(0);
}
if (lean_is_scalar(x_620)) {
 x_621 = lean_alloc_ctor(1, 1, 0);
} else {
 x_621 = x_620;
}
lean_ctor_set(x_621, 0, x_619);
return x_621;
}
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec_ref(x_482);
lean_dec(x_478);
lean_dec(x_471);
lean_dec_ref(x_467);
lean_dec(x_466);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_622 = lean_ctor_get(x_577, 0);
lean_inc(x_622);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 x_623 = x_577;
} else {
 lean_dec_ref(x_577);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(1, 1, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_622);
return x_624;
}
}
else
{
lean_dec(x_471);
lean_dec_ref(x_467);
lean_dec(x_466);
lean_dec(x_24);
x_533 = x_5;
x_534 = x_6;
x_535 = x_7;
x_536 = x_8;
x_537 = x_9;
x_538 = x_10;
x_539 = x_11;
x_540 = x_12;
x_541 = x_13;
x_542 = x_14;
x_543 = lean_box(0);
goto block_573;
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; 
lean_dec(x_532);
lean_dec_ref(x_482);
lean_dec(x_478);
lean_dec(x_471);
lean_dec_ref(x_467);
lean_dec(x_466);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_625 = lean_ctor_get(x_574, 0);
lean_inc(x_625);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 x_626 = x_574;
} else {
 lean_dec_ref(x_574);
 x_626 = lean_box(0);
}
if (lean_is_scalar(x_626)) {
 x_627 = lean_alloc_ctor(1, 1, 0);
} else {
 x_627 = x_626;
}
lean_ctor_set(x_627, 0, x_625);
return x_627;
}
}
block_573:
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_544 = lean_ctor_get(x_532, 2);
lean_inc(x_544);
lean_dec(x_532);
x_545 = l_Lean_mkNatLit(x_544);
x_546 = l_Lean_Meta_Sym_shareCommon___redArg(x_545, x_538);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
lean_dec_ref(x_546);
x_548 = lean_unsigned_to_nat(0u);
x_549 = lean_box(0);
lean_inc(x_542);
lean_inc_ref(x_541);
lean_inc(x_540);
lean_inc_ref(x_539);
lean_inc(x_538);
lean_inc_ref(x_537);
lean_inc(x_536);
lean_inc_ref(x_535);
lean_inc(x_534);
lean_inc(x_533);
lean_inc(x_547);
x_550 = lean_grind_internalize(x_547, x_548, x_549, x_533, x_534, x_535, x_536, x_537, x_538, x_539, x_540, x_541, x_542);
if (lean_obj_tag(x_550) == 0)
{
lean_object* x_551; 
lean_dec_ref(x_550);
lean_inc(x_542);
lean_inc_ref(x_541);
lean_inc(x_540);
lean_inc_ref(x_539);
lean_inc_ref(x_535);
lean_inc(x_533);
x_551 = lean_grind_mk_eq_proof(x_478, x_482, x_533, x_534, x_535, x_536, x_537, x_538, x_539, x_540, x_541, x_542);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
lean_dec_ref(x_551);
x_553 = l_Lean_Expr_appFn_x21(x_1);
lean_inc(x_542);
lean_inc_ref(x_541);
lean_inc(x_540);
lean_inc_ref(x_539);
x_554 = l_Lean_Meta_mkCongrArg(x_553, x_552, x_539, x_540, x_541, x_542);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
lean_dec_ref(x_554);
lean_inc(x_542);
lean_inc_ref(x_541);
lean_inc(x_540);
lean_inc_ref(x_539);
lean_inc(x_547);
lean_inc_ref(x_1);
x_556 = l_Lean_Meta_mkEq(x_1, x_547, x_539, x_540, x_541, x_542);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; lean_object* x_558; uint8_t x_559; lean_object* x_560; 
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
lean_dec_ref(x_556);
x_558 = l_Lean_Meta_mkExpectedPropHint(x_555, x_557);
x_559 = 0;
x_560 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_547, x_558, x_559, x_533, x_535, x_539, x_540, x_541, x_542);
lean_dec_ref(x_535);
lean_dec(x_533);
return x_560;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_555);
lean_dec(x_547);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_540);
lean_dec_ref(x_539);
lean_dec_ref(x_535);
lean_dec(x_533);
lean_dec_ref(x_1);
x_561 = lean_ctor_get(x_556, 0);
lean_inc(x_561);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 x_562 = x_556;
} else {
 lean_dec_ref(x_556);
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
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
lean_dec(x_547);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_540);
lean_dec_ref(x_539);
lean_dec_ref(x_535);
lean_dec(x_533);
lean_dec_ref(x_1);
x_564 = lean_ctor_get(x_554, 0);
lean_inc(x_564);
if (lean_is_exclusive(x_554)) {
 lean_ctor_release(x_554, 0);
 x_565 = x_554;
} else {
 lean_dec_ref(x_554);
 x_565 = lean_box(0);
}
if (lean_is_scalar(x_565)) {
 x_566 = lean_alloc_ctor(1, 1, 0);
} else {
 x_566 = x_565;
}
lean_ctor_set(x_566, 0, x_564);
return x_566;
}
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_547);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_540);
lean_dec_ref(x_539);
lean_dec_ref(x_535);
lean_dec(x_533);
lean_dec_ref(x_1);
x_567 = lean_ctor_get(x_551, 0);
lean_inc(x_567);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 x_568 = x_551;
} else {
 lean_dec_ref(x_551);
 x_568 = lean_box(0);
}
if (lean_is_scalar(x_568)) {
 x_569 = lean_alloc_ctor(1, 1, 0);
} else {
 x_569 = x_568;
}
lean_ctor_set(x_569, 0, x_567);
return x_569;
}
}
else
{
lean_dec(x_547);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_540);
lean_dec_ref(x_539);
lean_dec(x_538);
lean_dec_ref(x_537);
lean_dec(x_536);
lean_dec_ref(x_535);
lean_dec(x_534);
lean_dec(x_533);
lean_dec_ref(x_482);
lean_dec(x_478);
lean_dec_ref(x_1);
return x_550;
}
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; 
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_540);
lean_dec_ref(x_539);
lean_dec(x_538);
lean_dec_ref(x_537);
lean_dec(x_536);
lean_dec_ref(x_535);
lean_dec(x_534);
lean_dec(x_533);
lean_dec_ref(x_482);
lean_dec(x_478);
lean_dec_ref(x_1);
x_570 = lean_ctor_get(x_546, 0);
lean_inc(x_570);
if (lean_is_exclusive(x_546)) {
 lean_ctor_release(x_546, 0);
 x_571 = x_546;
} else {
 lean_dec_ref(x_546);
 x_571 = lean_box(0);
}
if (lean_is_scalar(x_571)) {
 x_572 = lean_alloc_ctor(1, 1, 0);
} else {
 x_572 = x_571;
}
lean_ctor_set(x_572, 0, x_570);
return x_572;
}
}
}
else
{
lean_object* x_628; lean_object* x_629; 
lean_dec(x_530);
lean_dec_ref(x_482);
lean_dec(x_478);
lean_dec(x_471);
lean_dec_ref(x_467);
lean_dec(x_466);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_628 = lean_box(0);
if (lean_is_scalar(x_531)) {
 x_629 = lean_alloc_ctor(0, 1, 0);
} else {
 x_629 = x_531;
}
lean_ctor_set(x_629, 0, x_628);
return x_629;
}
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; 
lean_dec_ref(x_482);
lean_dec(x_478);
lean_dec(x_471);
lean_dec_ref(x_467);
lean_dec(x_466);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_630 = lean_ctor_get(x_529, 0);
lean_inc(x_630);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 x_631 = x_529;
} else {
 lean_dec_ref(x_529);
 x_631 = lean_box(0);
}
if (lean_is_scalar(x_631)) {
 x_632 = lean_alloc_ctor(1, 1, 0);
} else {
 x_632 = x_631;
}
lean_ctor_set(x_632, 0, x_630);
return x_632;
}
}
block_526:
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_inc(x_489);
x_501 = l_Lean_mkConst(x_489, x_486);
x_502 = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
x_503 = l_Lean_Expr_getAppNumArgs(x_485);
lean_inc(x_503);
x_504 = lean_mk_array(x_503, x_502);
x_505 = lean_nat_sub(x_503, x_472);
lean_dec(x_503);
x_506 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_485, x_504, x_505);
x_507 = l_Lean_mkAppN(x_501, x_506);
lean_dec_ref(x_506);
x_508 = l_Lean_Expr_app___override(x_507, x_478);
x_509 = l_Lean_Expr_getAppNumArgs(x_487);
lean_inc(x_509);
x_510 = lean_mk_array(x_509, x_502);
x_511 = lean_nat_sub(x_509, x_472);
lean_dec(x_509);
x_512 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_487, x_510, x_511);
x_513 = l_Lean_mkAppN(x_508, x_512);
lean_dec_ref(x_512);
x_514 = l_Lean_Expr_app___override(x_513, x_482);
lean_inc(x_499);
lean_inc_ref(x_498);
lean_inc(x_497);
lean_inc_ref(x_496);
lean_inc_ref(x_514);
x_515 = lean_infer_type(x_514, x_496, x_497, x_498, x_499);
if (lean_obj_tag(x_515) == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
lean_dec_ref(x_515);
if (lean_is_scalar(x_466)) {
 x_517 = lean_alloc_ctor(0, 1, 0);
} else {
 x_517 = x_466;
 lean_ctor_set_tag(x_517, 0);
}
lean_ctor_set(x_517, 0, x_489);
if (lean_is_scalar(x_24)) {
 x_518 = lean_alloc_ctor(7, 1, 0);
} else {
 x_518 = x_24;
 lean_ctor_set_tag(x_518, 7);
}
lean_ctor_set(x_518, 0, x_517);
x_519 = l_Lean_Meta_Grind_addNewRawFact(x_514, x_516, x_488, x_518, x_490, x_491, x_492, x_493, x_494, x_495, x_496, x_497, x_498, x_499);
lean_dec(x_495);
lean_dec_ref(x_494);
lean_dec(x_493);
lean_dec_ref(x_492);
lean_dec(x_491);
lean_dec(x_490);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; 
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 x_520 = x_519;
} else {
 lean_dec_ref(x_519);
 x_520 = lean_box(0);
}
x_521 = lean_box(0);
if (lean_is_scalar(x_520)) {
 x_522 = lean_alloc_ctor(0, 1, 0);
} else {
 x_522 = x_520;
}
lean_ctor_set(x_522, 0, x_521);
return x_522;
}
else
{
return x_519;
}
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; 
lean_dec_ref(x_514);
lean_dec(x_499);
lean_dec_ref(x_498);
lean_dec(x_497);
lean_dec_ref(x_496);
lean_dec(x_495);
lean_dec_ref(x_494);
lean_dec(x_493);
lean_dec_ref(x_492);
lean_dec(x_491);
lean_dec(x_490);
lean_dec(x_489);
lean_dec(x_488);
lean_dec(x_466);
lean_dec(x_24);
x_523 = lean_ctor_get(x_515, 0);
lean_inc(x_523);
if (lean_is_exclusive(x_515)) {
 lean_ctor_release(x_515, 0);
 x_524 = x_515;
} else {
 lean_dec_ref(x_515);
 x_524 = lean_box(0);
}
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 1, 0);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_523);
return x_525;
}
}
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; 
lean_dec(x_478);
lean_dec(x_471);
lean_dec_ref(x_467);
lean_dec(x_466);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_633 = lean_ctor_get(x_479, 0);
lean_inc(x_633);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 x_634 = x_479;
} else {
 lean_dec_ref(x_479);
 x_634 = lean_box(0);
}
if (lean_is_scalar(x_634)) {
 x_635 = lean_alloc_ctor(1, 1, 0);
} else {
 x_635 = x_634;
}
lean_ctor_set(x_635, 0, x_633);
return x_635;
}
}
}
else
{
lean_object* x_636; lean_object* x_637; 
lean_dec(x_464);
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_636 = lean_box(0);
x_637 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_637, 0, x_636);
return x_637;
}
}
}
else
{
uint8_t x_638; 
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_638 = !lean_is_exclusive(x_25);
if (x_638 == 0)
{
return x_25;
}
else
{
lean_object* x_639; lean_object* x_640; 
x_639 = lean_ctor_get(x_25, 0);
lean_inc(x_639);
lean_dec(x_25);
x_640 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_640, 0, x_639);
return x_640;
}
}
}
else
{
lean_object* x_641; lean_object* x_642; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_641 = lean_box(0);
x_642 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_642, 0, x_641);
return x_642;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
x_14 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_14);
x_15 = lean_mk_array(x_14, x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_14, x_16);
lean_dec(x_14);
lean_inc_ref(x_1);
x_18 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(x_1, x_1, x_15, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateCtorIdxUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
