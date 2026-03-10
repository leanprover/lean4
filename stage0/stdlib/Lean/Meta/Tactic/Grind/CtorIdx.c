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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_315; 
x_23 = lean_ctor_get(x_22, 0);
x_315 = !lean_is_exclusive(x_22);
if (x_315 == 0)
{
x_24 = x_22;
x_25 = x_315;
goto block_314;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_315;
goto block_314;
}
block_314:
{
lean_object* x_26; 
x_26 = l_isCtorIdx_x3f___redArg(x_23, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_305; 
x_27 = lean_ctor_get(x_26, 0);
x_305 = !lean_is_exclusive(x_26);
if (x_305 == 0)
{
x_28 = x_26;
x_29 = x_305;
goto block_304;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_305;
goto block_304;
}
block_304:
{
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_299; 
x_30 = lean_ctor_get(x_27, 0);
x_299 = !lean_is_exclusive(x_27);
if (x_299 == 0)
{
x_31 = x_27;
x_32 = x_299;
goto block_298;
}
else
{
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_box(0);
x_32 = x_299;
goto block_298;
}
block_298:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_30, 2);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_array_get_size(x_3);
x_37 = lean_nat_add(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_37, x_38);
x_40 = lean_nat_dec_eq(x_36, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
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
x_41 = lean_box(0);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_41);
x_42 = x_28;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_del_object(x_28);
x_45 = l_Lean_instInhabitedExpr;
x_46 = lean_nat_sub(x_36, x_38);
x_47 = lean_array_get(x_45, x_3, x_46);
lean_dec(x_46);
lean_dec_ref(x_3);
lean_inc(x_47);
x_48 = l_Lean_Meta_Grind_getRootENode___redArg(x_47, x_5, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_289; 
x_49 = lean_ctor_get(x_48, 0);
x_289 = !lean_is_exclusive(x_48);
if (x_289 == 0)
{
x_50 = x_48;
x_51 = x_289;
goto block_288;
}
else
{
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_box(0);
x_51 = x_289;
goto block_288;
}
block_288:
{
lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc_ref(x_52);
x_53 = lean_ctor_get_uint8(x_49, sizeof(void*)*11 + 2);
x_54 = lean_ctor_get_uint8(x_49, sizeof(void*)*11 + 4);
lean_dec(x_49);
if (x_53 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
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
x_111 = lean_box(0);
if (x_51 == 0)
{
lean_ctor_set(x_50, 0, x_111);
x_112 = x_50;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_111);
x_112 = x_114;
goto block_113;
}
block_113:
{
return x_112;
}
}
else
{
lean_object* x_115; 
lean_del_object(x_50);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_52);
x_115 = l_Lean_Meta_isConstructorApp_x3f(x_52, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_279; 
x_116 = lean_ctor_get(x_115, 0);
x_279 = !lean_is_exclusive(x_115);
if (x_279 == 0)
{
x_117 = x_115;
x_118 = x_279;
goto block_278;
}
else
{
lean_inc(x_116);
lean_dec(x_115);
x_117 = lean_box(0);
x_118 = x_279;
goto block_278;
}
block_278:
{
if (lean_obj_tag(x_116) == 1)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_del_object(x_117);
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
lean_dec_ref(x_116);
if (x_54 == 0)
{
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
x_120 = x_5;
x_121 = x_6;
x_122 = x_7;
x_123 = x_8;
x_124 = x_9;
x_125 = x_10;
x_126 = x_11;
x_127 = x_12;
x_128 = x_13;
x_129 = x_14;
goto block_179;
}
else
{
lean_object* x_180; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_52);
lean_inc(x_47);
x_180 = l_Lean_Meta_Grind_hasSameType(x_47, x_52, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec_ref(x_180);
x_182 = lean_unbox(x_181);
lean_dec(x_181);
if (x_182 == 0)
{
lean_object* x_183; 
lean_dec(x_119);
lean_dec_ref(x_1);
x_183 = l_Lean_Meta_Grind_getGeneration___redArg(x_47, x_5);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec_ref(x_183);
x_185 = l_Lean_Meta_Grind_getGeneration___redArg(x_52, x_5);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; uint8_t x_249; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
lean_dec_ref(x_185);
x_249 = lean_nat_dec_le(x_184, x_186);
if (x_249 == 0)
{
lean_dec(x_186);
x_187 = x_184;
goto block_248;
}
else
{
lean_dec(x_184);
x_187 = x_186;
goto block_248;
}
block_248:
{
lean_object* x_188; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_47);
x_188 = lean_infer_type(x_47, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
lean_dec_ref(x_188);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_190 = l_Lean_Meta_whnfD(x_189, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec_ref(x_190);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_52);
x_192 = lean_infer_type(x_52, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
lean_dec_ref(x_192);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_194 = l_Lean_Meta_whnfD(x_193, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; uint8_t x_215; 
x_195 = lean_ctor_get(x_194, 0);
x_215 = !lean_is_exclusive(x_194);
if (x_215 == 0)
{
x_196 = x_194;
x_197 = x_215;
goto block_214;
}
else
{
lean_inc(x_195);
lean_dec(x_194);
x_196 = lean_box(0);
x_197 = x_215;
goto block_214;
}
block_214:
{
lean_object* x_198; uint8_t x_199; 
x_198 = lean_ctor_get(x_33, 0);
lean_inc(x_198);
lean_dec_ref(x_33);
lean_inc(x_37);
x_199 = l_Lean_Expr_isAppOfArity(x_191, x_198, x_37);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_198);
lean_del_object(x_196);
lean_dec(x_195);
lean_dec(x_191);
lean_dec(x_187);
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec(x_37);
lean_del_object(x_31);
lean_del_object(x_24);
x_200 = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4);
x_201 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_200, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_201;
}
else
{
uint8_t x_202; 
x_202 = l_Lean_Expr_isAppOfArity(x_195, x_198, x_37);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_198);
lean_dec(x_195);
lean_dec(x_191);
lean_dec(x_187);
lean_dec_ref(x_52);
lean_dec(x_47);
lean_del_object(x_31);
lean_del_object(x_24);
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
x_203 = lean_box(0);
if (x_197 == 0)
{
lean_ctor_set(x_196, 0, x_203);
x_204 = x_196;
goto block_205;
}
else
{
lean_object* x_206; 
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_203);
x_204 = x_206;
goto block_205;
}
block_205:
{
return x_204;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
lean_del_object(x_196);
x_207 = lean_st_ref_get(x_14);
x_208 = lean_ctor_get(x_207, 0);
lean_inc_ref(x_208);
lean_dec(x_207);
x_209 = l_Lean_Expr_getAppFn(x_191);
x_210 = l_Lean_Expr_constLevels_x21(x_209);
lean_dec_ref(x_209);
x_211 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_198);
x_212 = l_Lean_Environment_containsOnBranch(x_208, x_211);
if (x_212 == 0)
{
lean_object* x_213; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_211);
x_213 = l_Lean_executeReservedNameAction(x_211, x_13, x_14);
if (lean_obj_tag(x_213) == 0)
{
lean_dec_ref(x_213);
x_55 = x_211;
x_56 = x_210;
x_57 = x_191;
x_58 = x_187;
x_59 = x_195;
x_60 = x_5;
x_61 = x_6;
x_62 = x_7;
x_63 = x_8;
x_64 = x_9;
x_65 = x_10;
x_66 = x_11;
x_67 = x_12;
x_68 = x_13;
x_69 = x_14;
goto block_110;
}
else
{
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_195);
lean_dec(x_191);
lean_dec(x_187);
lean_dec_ref(x_52);
lean_dec(x_47);
lean_del_object(x_31);
lean_del_object(x_24);
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
return x_213;
}
}
else
{
x_55 = x_211;
x_56 = x_210;
x_57 = x_191;
x_58 = x_187;
x_59 = x_195;
x_60 = x_5;
x_61 = x_6;
x_62 = x_7;
x_63 = x_8;
x_64 = x_9;
x_65 = x_10;
x_66 = x_11;
x_67 = x_12;
x_68 = x_13;
x_69 = x_14;
goto block_110;
}
}
}
}
}
else
{
lean_object* x_216; lean_object* x_217; uint8_t x_218; uint8_t x_223; 
lean_dec(x_191);
lean_dec(x_187);
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
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
x_216 = lean_ctor_get(x_194, 0);
x_223 = !lean_is_exclusive(x_194);
if (x_223 == 0)
{
x_217 = x_194;
x_218 = x_223;
goto block_222;
}
else
{
lean_inc(x_216);
lean_dec(x_194);
x_217 = lean_box(0);
x_218 = x_223;
goto block_222;
}
block_222:
{
lean_object* x_219; 
if (x_218 == 0)
{
x_219 = x_217;
goto block_220;
}
else
{
lean_object* x_221; 
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_216);
x_219 = x_221;
goto block_220;
}
block_220:
{
return x_219;
}
}
}
}
else
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; uint8_t x_231; 
lean_dec(x_191);
lean_dec(x_187);
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
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
x_224 = lean_ctor_get(x_192, 0);
x_231 = !lean_is_exclusive(x_192);
if (x_231 == 0)
{
x_225 = x_192;
x_226 = x_231;
goto block_230;
}
else
{
lean_inc(x_224);
lean_dec(x_192);
x_225 = lean_box(0);
x_226 = x_231;
goto block_230;
}
block_230:
{
lean_object* x_227; 
if (x_226 == 0)
{
x_227 = x_225;
goto block_228;
}
else
{
lean_object* x_229; 
x_229 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_229, 0, x_224);
x_227 = x_229;
goto block_228;
}
block_228:
{
return x_227;
}
}
}
}
else
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; uint8_t x_239; 
lean_dec(x_187);
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
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
x_232 = lean_ctor_get(x_190, 0);
x_239 = !lean_is_exclusive(x_190);
if (x_239 == 0)
{
x_233 = x_190;
x_234 = x_239;
goto block_238;
}
else
{
lean_inc(x_232);
lean_dec(x_190);
x_233 = lean_box(0);
x_234 = x_239;
goto block_238;
}
block_238:
{
lean_object* x_235; 
if (x_234 == 0)
{
x_235 = x_233;
goto block_236;
}
else
{
lean_object* x_237; 
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_232);
x_235 = x_237;
goto block_236;
}
block_236:
{
return x_235;
}
}
}
}
else
{
lean_object* x_240; lean_object* x_241; uint8_t x_242; uint8_t x_247; 
lean_dec(x_187);
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
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
x_240 = lean_ctor_get(x_188, 0);
x_247 = !lean_is_exclusive(x_188);
if (x_247 == 0)
{
x_241 = x_188;
x_242 = x_247;
goto block_246;
}
else
{
lean_inc(x_240);
lean_dec(x_188);
x_241 = lean_box(0);
x_242 = x_247;
goto block_246;
}
block_246:
{
lean_object* x_243; 
if (x_242 == 0)
{
x_243 = x_241;
goto block_244;
}
else
{
lean_object* x_245; 
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_240);
x_243 = x_245;
goto block_244;
}
block_244:
{
return x_243;
}
}
}
}
}
else
{
lean_object* x_250; lean_object* x_251; uint8_t x_252; uint8_t x_257; 
lean_dec(x_184);
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
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
x_250 = lean_ctor_get(x_185, 0);
x_257 = !lean_is_exclusive(x_185);
if (x_257 == 0)
{
x_251 = x_185;
x_252 = x_257;
goto block_256;
}
else
{
lean_inc(x_250);
lean_dec(x_185);
x_251 = lean_box(0);
x_252 = x_257;
goto block_256;
}
block_256:
{
lean_object* x_253; 
if (x_252 == 0)
{
x_253 = x_251;
goto block_254;
}
else
{
lean_object* x_255; 
x_255 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_255, 0, x_250);
x_253 = x_255;
goto block_254;
}
block_254:
{
return x_253;
}
}
}
}
else
{
lean_object* x_258; lean_object* x_259; uint8_t x_260; uint8_t x_265; 
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
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
x_258 = lean_ctor_get(x_183, 0);
x_265 = !lean_is_exclusive(x_183);
if (x_265 == 0)
{
x_259 = x_183;
x_260 = x_265;
goto block_264;
}
else
{
lean_inc(x_258);
lean_dec(x_183);
x_259 = lean_box(0);
x_260 = x_265;
goto block_264;
}
block_264:
{
lean_object* x_261; 
if (x_260 == 0)
{
x_261 = x_259;
goto block_262;
}
else
{
lean_object* x_263; 
x_263 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_263, 0, x_258);
x_261 = x_263;
goto block_262;
}
block_262:
{
return x_261;
}
}
}
}
else
{
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
x_120 = x_5;
x_121 = x_6;
x_122 = x_7;
x_123 = x_8;
x_124 = x_9;
x_125 = x_10;
x_126 = x_11;
x_127 = x_12;
x_128 = x_13;
x_129 = x_14;
goto block_179;
}
}
else
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; uint8_t x_273; 
lean_dec(x_119);
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
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
x_266 = lean_ctor_get(x_180, 0);
x_273 = !lean_is_exclusive(x_180);
if (x_273 == 0)
{
x_267 = x_180;
x_268 = x_273;
goto block_272;
}
else
{
lean_inc(x_266);
lean_dec(x_180);
x_267 = lean_box(0);
x_268 = x_273;
goto block_272;
}
block_272:
{
lean_object* x_269; 
if (x_268 == 0)
{
x_269 = x_267;
goto block_270;
}
else
{
lean_object* x_271; 
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_266);
x_269 = x_271;
goto block_270;
}
block_270:
{
return x_269;
}
}
}
}
block_179:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_119, 2);
lean_inc(x_130);
lean_dec(x_119);
x_131 = l_Lean_mkNatLit(x_130);
x_132 = l_Lean_Meta_Sym_shareCommon___redArg(x_131, x_125);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
x_134 = lean_unsigned_to_nat(0u);
x_135 = lean_box(0);
lean_inc(x_129);
lean_inc_ref(x_128);
lean_inc(x_127);
lean_inc_ref(x_126);
lean_inc(x_125);
lean_inc_ref(x_124);
lean_inc(x_123);
lean_inc_ref(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_133);
x_136 = lean_grind_internalize(x_133, x_134, x_135, x_120, x_121, x_122, x_123, x_124, x_125, x_126, x_127, x_128, x_129);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
lean_dec_ref(x_136);
lean_inc(x_129);
lean_inc_ref(x_128);
lean_inc(x_127);
lean_inc_ref(x_126);
lean_inc_ref(x_122);
lean_inc(x_120);
x_137 = lean_grind_mk_eq_proof(x_47, x_52, x_120, x_121, x_122, x_123, x_124, x_125, x_126, x_127, x_128, x_129);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
x_139 = l_Lean_Expr_appFn_x21(x_1);
lean_inc(x_129);
lean_inc_ref(x_128);
lean_inc(x_127);
lean_inc_ref(x_126);
x_140 = l_Lean_Meta_mkCongrArg(x_139, x_138, x_126, x_127, x_128, x_129);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
lean_inc(x_129);
lean_inc_ref(x_128);
lean_inc(x_127);
lean_inc_ref(x_126);
lean_inc(x_133);
lean_inc_ref(x_1);
x_142 = l_Lean_Meta_mkEq(x_1, x_133, x_126, x_127, x_128, x_129);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = l_Lean_Meta_mkExpectedPropHint(x_141, x_143);
x_145 = 0;
x_146 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_133, x_144, x_145, x_120, x_122, x_126, x_127, x_128, x_129);
lean_dec_ref(x_122);
lean_dec(x_120);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_154; 
lean_dec(x_141);
lean_dec(x_133);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_122);
lean_dec(x_120);
lean_dec_ref(x_1);
x_147 = lean_ctor_get(x_142, 0);
x_154 = !lean_is_exclusive(x_142);
if (x_154 == 0)
{
x_148 = x_142;
x_149 = x_154;
goto block_153;
}
else
{
lean_inc(x_147);
lean_dec(x_142);
x_148 = lean_box(0);
x_149 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_150; 
if (x_149 == 0)
{
x_150 = x_148;
goto block_151;
}
else
{
lean_object* x_152; 
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_147);
x_150 = x_152;
goto block_151;
}
block_151:
{
return x_150;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; uint8_t x_162; 
lean_dec(x_133);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_122);
lean_dec(x_120);
lean_dec_ref(x_1);
x_155 = lean_ctor_get(x_140, 0);
x_162 = !lean_is_exclusive(x_140);
if (x_162 == 0)
{
x_156 = x_140;
x_157 = x_162;
goto block_161;
}
else
{
lean_inc(x_155);
lean_dec(x_140);
x_156 = lean_box(0);
x_157 = x_162;
goto block_161;
}
block_161:
{
lean_object* x_158; 
if (x_157 == 0)
{
x_158 = x_156;
goto block_159;
}
else
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_155);
x_158 = x_160;
goto block_159;
}
block_159:
{
return x_158;
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_170; 
lean_dec(x_133);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_122);
lean_dec(x_120);
lean_dec_ref(x_1);
x_163 = lean_ctor_get(x_137, 0);
x_170 = !lean_is_exclusive(x_137);
if (x_170 == 0)
{
x_164 = x_137;
x_165 = x_170;
goto block_169;
}
else
{
lean_inc(x_163);
lean_dec(x_137);
x_164 = lean_box(0);
x_165 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_166; 
if (x_165 == 0)
{
x_166 = x_164;
goto block_167;
}
else
{
lean_object* x_168; 
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_163);
x_166 = x_168;
goto block_167;
}
block_167:
{
return x_166;
}
}
}
}
else
{
lean_dec(x_133);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec_ref(x_1);
return x_136;
}
}
else
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; uint8_t x_178; 
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec_ref(x_1);
x_171 = lean_ctor_get(x_132, 0);
x_178 = !lean_is_exclusive(x_132);
if (x_178 == 0)
{
x_172 = x_132;
x_173 = x_178;
goto block_177;
}
else
{
lean_inc(x_171);
lean_dec(x_132);
x_172 = lean_box(0);
x_173 = x_178;
goto block_177;
}
block_177:
{
lean_object* x_174; 
if (x_173 == 0)
{
x_174 = x_172;
goto block_175;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_171);
x_174 = x_176;
goto block_175;
}
block_175:
{
return x_174;
}
}
}
}
}
else
{
lean_object* x_274; lean_object* x_275; 
lean_dec(x_116);
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
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
x_274 = lean_box(0);
if (x_118 == 0)
{
lean_ctor_set(x_117, 0, x_274);
x_275 = x_117;
goto block_276;
}
else
{
lean_object* x_277; 
x_277 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_277, 0, x_274);
x_275 = x_277;
goto block_276;
}
block_276:
{
return x_275;
}
}
}
}
else
{
lean_object* x_280; lean_object* x_281; uint8_t x_282; uint8_t x_287; 
lean_dec_ref(x_52);
lean_dec(x_47);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
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
x_280 = lean_ctor_get(x_115, 0);
x_287 = !lean_is_exclusive(x_115);
if (x_287 == 0)
{
x_281 = x_115;
x_282 = x_287;
goto block_286;
}
else
{
lean_inc(x_280);
lean_dec(x_115);
x_281 = lean_box(0);
x_282 = x_287;
goto block_286;
}
block_286:
{
lean_object* x_283; 
if (x_282 == 0)
{
x_283 = x_281;
goto block_284;
}
else
{
lean_object* x_285; 
x_285 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_285, 0, x_280);
x_283 = x_285;
goto block_284;
}
block_284:
{
return x_283;
}
}
}
}
block_110:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_inc(x_55);
x_70 = l_Lean_mkConst(x_55, x_56);
x_71 = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0, &l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
x_72 = l_Lean_Expr_getAppNumArgs(x_57);
lean_inc(x_72);
x_73 = lean_mk_array(x_72, x_71);
x_74 = lean_nat_sub(x_72, x_38);
lean_dec(x_72);
x_75 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_57, x_73, x_74);
x_76 = l_Lean_mkAppN(x_70, x_75);
lean_dec_ref(x_75);
x_77 = l_Lean_Expr_app___override(x_76, x_47);
x_78 = l_Lean_Expr_getAppNumArgs(x_59);
lean_inc(x_78);
x_79 = lean_mk_array(x_78, x_71);
x_80 = lean_nat_sub(x_78, x_38);
lean_dec(x_78);
x_81 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_59, x_79, x_80);
x_82 = l_Lean_mkAppN(x_77, x_81);
lean_dec_ref(x_81);
x_83 = l_Lean_Expr_app___override(x_82, x_52);
lean_inc(x_69);
lean_inc_ref(x_68);
lean_inc(x_67);
lean_inc_ref(x_66);
lean_inc_ref(x_83);
x_84 = lean_infer_type(x_83, x_66, x_67, x_68, x_69);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
if (x_32 == 0)
{
lean_ctor_set_tag(x_31, 0);
lean_ctor_set(x_31, 0, x_55);
x_86 = x_31;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_55);
x_86 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_87; 
if (x_25 == 0)
{
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 0, x_86);
x_87 = x_24;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(x_99, 0, x_86);
x_87 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_88; 
x_88 = l_Lean_Meta_Grind_addNewRawFact(x_83, x_85, x_58, x_87, x_60, x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec(x_60);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; uint8_t x_96; 
x_96 = !lean_is_exclusive(x_88);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_88, 0);
lean_dec(x_97);
x_89 = x_88;
x_90 = x_96;
goto block_95;
}
else
{
lean_dec(x_88);
x_89 = lean_box(0);
x_90 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_box(0);
if (x_90 == 0)
{
lean_ctor_set(x_89, 0, x_91);
x_92 = x_89;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_91);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
}
else
{
return x_88;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_109; 
lean_dec_ref(x_83);
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_55);
lean_del_object(x_31);
lean_del_object(x_24);
x_102 = lean_ctor_get(x_84, 0);
x_109 = !lean_is_exclusive(x_84);
if (x_109 == 0)
{
x_103 = x_84;
x_104 = x_109;
goto block_108;
}
else
{
lean_inc(x_102);
lean_dec(x_84);
x_103 = lean_box(0);
x_104 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_105; 
if (x_104 == 0)
{
x_105 = x_103;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_102);
x_105 = x_107;
goto block_106;
}
block_106:
{
return x_105;
}
}
}
}
}
}
else
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_297; 
lean_dec(x_47);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_del_object(x_31);
lean_del_object(x_24);
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
x_290 = lean_ctor_get(x_48, 0);
x_297 = !lean_is_exclusive(x_48);
if (x_297 == 0)
{
x_291 = x_48;
x_292 = x_297;
goto block_296;
}
else
{
lean_inc(x_290);
lean_dec(x_48);
x_291 = lean_box(0);
x_292 = x_297;
goto block_296;
}
block_296:
{
lean_object* x_293; 
if (x_292 == 0)
{
x_293 = x_291;
goto block_294;
}
else
{
lean_object* x_295; 
x_295 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_295, 0, x_290);
x_293 = x_295;
goto block_294;
}
block_294:
{
return x_293;
}
}
}
}
}
}
else
{
lean_object* x_300; lean_object* x_301; 
lean_dec(x_27);
lean_del_object(x_24);
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
x_300 = lean_box(0);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_300);
x_301 = x_28;
goto block_302;
}
else
{
lean_object* x_303; 
x_303 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_303, 0, x_300);
x_301 = x_303;
goto block_302;
}
block_302:
{
return x_301;
}
}
}
}
else
{
lean_object* x_306; lean_object* x_307; uint8_t x_308; uint8_t x_313; 
lean_del_object(x_24);
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
x_306 = lean_ctor_get(x_26, 0);
x_313 = !lean_is_exclusive(x_26);
if (x_313 == 0)
{
x_307 = x_26;
x_308 = x_313;
goto block_312;
}
else
{
lean_inc(x_306);
lean_dec(x_26);
x_307 = lean_box(0);
x_308 = x_313;
goto block_312;
}
block_312:
{
lean_object* x_309; 
if (x_308 == 0)
{
x_309 = x_307;
goto block_310;
}
else
{
lean_object* x_311; 
x_311 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_311, 0, x_306);
x_309 = x_311;
goto block_310;
}
block_310:
{
return x_309;
}
}
}
}
}
else
{
lean_object* x_316; lean_object* x_317; 
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
x_316 = lean_box(0);
x_317 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_317, 0, x_316);
return x_317;
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
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CtorIdxHInj(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CtorIdxHInj(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_CtorIdxHInj(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorIdxHInj(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_CtorIdx(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_CtorIdx(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_CtorIdx(builtin);
}
#ifdef __cplusplus
}
#endif
