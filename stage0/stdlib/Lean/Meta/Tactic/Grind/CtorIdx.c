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
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(lean_object*);
lean_object* l_Lean_executeReservedNameAction(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3;
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_isCtorIdx_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1;
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___closed__0;
x_12 = lean_panic_fn(x_11, x_1);
x_13 = lean_apply_9(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateCtorIdxUp___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: aType.isAppOfArity indInfo.name (indInfo.numParams + indInfo.numIndices)\n      -- both types should be headed by the same type former\n      ", 161, 161);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.propagateCtorIdxUp", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.CtorIdx", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_unsigned_to_nat(34u);
x_4 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1;
x_5 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_3);
x_17 = lean_array_set(x_4, x_5, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_5, x_18);
lean_dec(x_5);
x_3 = x_15;
x_4 = x_17;
x_5 = x_19;
goto _start;
}
else
{
lean_object* x_21; 
lean_dec(x_5);
x_21 = l_Lean_Expr_constName_x3f(x_3);
lean_dec_ref(x_3);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_24 = l_isCtorIdx_x3f___redArg(x_22, x_13);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 2);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_array_get_size(x_4);
x_33 = lean_nat_add(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_33, x_34);
x_36 = lean_nat_dec_eq(x_32, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_37 = lean_box(0);
lean_ctor_set(x_24, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_free_object(x_24);
x_38 = l_Array_back_x21___redArg(x_1, x_4);
lean_dec_ref(x_4);
lean_inc(x_38);
x_39 = l_Lean_Meta_Grind_getRootENode___redArg(x_38, x_6, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_42);
x_43 = lean_ctor_get_uint8(x_41, sizeof(void*)*11 + 2);
x_44 = lean_ctor_get_uint8(x_41, sizeof(void*)*11 + 4);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_87; 
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_87 = lean_box(0);
lean_ctor_set(x_39, 0, x_87);
return x_39;
}
else
{
lean_object* x_88; 
lean_free_object(x_39);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_42);
x_88 = l_Lean_Meta_isConstructorApp_x3f(x_42, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_88, 0);
if (lean_obj_tag(x_90) == 1)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_free_object(x_88);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec_ref(x_90);
if (x_44 == 0)
{
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
x_92 = x_6;
x_93 = x_7;
x_94 = x_8;
x_95 = x_9;
x_96 = x_10;
x_97 = x_11;
x_98 = x_12;
x_99 = x_13;
x_100 = lean_box(0);
goto block_130;
}
else
{
lean_object* x_131; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_42);
lean_inc(x_38);
x_131 = l_Lean_Meta_Grind_hasSameType(x_38, x_42, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_91);
lean_dec_ref(x_2);
x_134 = l_Lean_Meta_Grind_getGeneration___redArg(x_38, x_6);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
x_136 = l_Lean_Meta_Grind_getGeneration___redArg(x_42, x_6);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_189; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec_ref(x_136);
x_189 = lean_nat_dec_le(x_135, x_137);
if (x_189 == 0)
{
lean_dec(x_137);
x_138 = x_135;
goto block_188;
}
else
{
lean_dec(x_135);
x_138 = x_137;
goto block_188;
}
block_188:
{
lean_object* x_139; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_38);
x_139 = lean_infer_type(x_38, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_141 = l_Lean_Meta_whnfD(x_140, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec_ref(x_141);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_42);
x_143 = lean_infer_type(x_42, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_145 = l_Lean_Meta_whnfD(x_144, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_145) == 0)
{
uint8_t x_146; 
x_146 = !lean_is_exclusive(x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = lean_ctor_get(x_145, 0);
x_148 = lean_ctor_get(x_29, 0);
lean_inc(x_148);
lean_dec_ref(x_29);
lean_inc(x_33);
x_149 = l_Lean_Expr_isAppOfArity(x_142, x_148, x_33);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_148);
lean_free_object(x_145);
lean_dec(x_147);
lean_dec(x_142);
lean_dec(x_138);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_23);
x_150 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3;
x_151 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_150, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_151;
}
else
{
uint8_t x_152; 
x_152 = l_Lean_Expr_isAppOfArity(x_147, x_148, x_33);
if (x_152 == 0)
{
lean_object* x_153; 
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_142);
lean_dec(x_138);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_153 = lean_box(0);
lean_ctor_set(x_145, 0, x_153);
return x_145;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
lean_free_object(x_145);
x_154 = lean_st_ref_get(x_13);
x_155 = lean_ctor_get(x_154, 0);
lean_inc_ref(x_155);
lean_dec(x_154);
x_156 = l_Lean_Expr_getAppFn(x_142);
x_157 = l_Lean_Expr_constLevels_x21(x_156);
lean_dec_ref(x_156);
x_158 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_148);
x_159 = l_Lean_Environment_containsOnBranch(x_155, x_158);
if (x_159 == 0)
{
lean_object* x_160; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_158);
x_160 = l_Lean_executeReservedNameAction(x_158, x_12, x_13);
if (lean_obj_tag(x_160) == 0)
{
lean_dec_ref(x_160);
x_45 = x_158;
x_46 = x_157;
x_47 = x_147;
x_48 = x_142;
x_49 = x_138;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_11;
x_56 = x_12;
x_57 = x_13;
x_58 = lean_box(0);
goto block_86;
}
else
{
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_147);
lean_dec(x_142);
lean_dec(x_138);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_160;
}
}
else
{
x_45 = x_158;
x_46 = x_157;
x_47 = x_147;
x_48 = x_142;
x_49 = x_138;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_11;
x_56 = x_12;
x_57 = x_13;
x_58 = lean_box(0);
goto block_86;
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_145, 0);
lean_inc(x_161);
lean_dec(x_145);
x_162 = lean_ctor_get(x_29, 0);
lean_inc(x_162);
lean_dec_ref(x_29);
lean_inc(x_33);
x_163 = l_Lean_Expr_isAppOfArity(x_142, x_162, x_33);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_142);
lean_dec(x_138);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_23);
x_164 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3;
x_165 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_164, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_165;
}
else
{
uint8_t x_166; 
x_166 = l_Lean_Expr_isAppOfArity(x_161, x_162, x_33);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_142);
lean_dec(x_138);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_167 = lean_box(0);
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_167);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_169 = lean_st_ref_get(x_13);
x_170 = lean_ctor_get(x_169, 0);
lean_inc_ref(x_170);
lean_dec(x_169);
x_171 = l_Lean_Expr_getAppFn(x_142);
x_172 = l_Lean_Expr_constLevels_x21(x_171);
lean_dec_ref(x_171);
x_173 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_162);
x_174 = l_Lean_Environment_containsOnBranch(x_170, x_173);
if (x_174 == 0)
{
lean_object* x_175; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_173);
x_175 = l_Lean_executeReservedNameAction(x_173, x_12, x_13);
if (lean_obj_tag(x_175) == 0)
{
lean_dec_ref(x_175);
x_45 = x_173;
x_46 = x_172;
x_47 = x_161;
x_48 = x_142;
x_49 = x_138;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_11;
x_56 = x_12;
x_57 = x_13;
x_58 = lean_box(0);
goto block_86;
}
else
{
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_161);
lean_dec(x_142);
lean_dec(x_138);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_175;
}
}
else
{
x_45 = x_173;
x_46 = x_172;
x_47 = x_161;
x_48 = x_142;
x_49 = x_138;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_11;
x_56 = x_12;
x_57 = x_13;
x_58 = lean_box(0);
goto block_86;
}
}
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_142);
lean_dec(x_138);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_176 = !lean_is_exclusive(x_145);
if (x_176 == 0)
{
return x_145;
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_145, 0);
lean_inc(x_177);
lean_dec(x_145);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
return x_178;
}
}
}
else
{
uint8_t x_179; 
lean_dec(x_142);
lean_dec(x_138);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_179 = !lean_is_exclusive(x_143);
if (x_179 == 0)
{
return x_143;
}
else
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_143, 0);
lean_inc(x_180);
lean_dec(x_143);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_180);
return x_181;
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_138);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_182 = !lean_is_exclusive(x_141);
if (x_182 == 0)
{
return x_141;
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_141, 0);
lean_inc(x_183);
lean_dec(x_141);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_138);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_185 = !lean_is_exclusive(x_139);
if (x_185 == 0)
{
return x_139;
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_139, 0);
lean_inc(x_186);
lean_dec(x_139);
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_186);
return x_187;
}
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_135);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_190 = !lean_is_exclusive(x_136);
if (x_190 == 0)
{
return x_136;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_136, 0);
lean_inc(x_191);
lean_dec(x_136);
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_191);
return x_192;
}
}
}
else
{
uint8_t x_193; 
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_193 = !lean_is_exclusive(x_134);
if (x_193 == 0)
{
return x_134;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_134, 0);
lean_inc(x_194);
lean_dec(x_134);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_194);
return x_195;
}
}
}
else
{
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
x_92 = x_6;
x_93 = x_7;
x_94 = x_8;
x_95 = x_9;
x_96 = x_10;
x_97 = x_11;
x_98 = x_12;
x_99 = x_13;
x_100 = lean_box(0);
goto block_130;
}
}
else
{
uint8_t x_196; 
lean_dec(x_91);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_196 = !lean_is_exclusive(x_131);
if (x_196 == 0)
{
return x_131;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_131, 0);
lean_inc(x_197);
lean_dec(x_131);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_197);
return x_198;
}
}
}
block_130:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_91, 2);
lean_inc(x_101);
lean_dec(x_91);
x_102 = l_Lean_mkNatLit(x_101);
x_103 = l_Lean_Meta_Grind_shareCommon___redArg(x_102, x_95);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = lean_unsigned_to_nat(0u);
x_106 = lean_box(0);
lean_inc(x_99);
lean_inc_ref(x_98);
lean_inc(x_97);
lean_inc_ref(x_96);
lean_inc(x_95);
lean_inc_ref(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_104);
x_107 = lean_grind_internalize(x_104, x_105, x_106, x_92, x_93, x_94, x_95, x_96, x_97, x_98, x_99);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
lean_dec_ref(x_107);
lean_inc(x_99);
lean_inc_ref(x_98);
lean_inc(x_97);
lean_inc_ref(x_96);
lean_inc_ref(x_94);
lean_inc(x_92);
x_108 = lean_grind_mk_eq_proof(x_38, x_42, x_92, x_93, x_94, x_95, x_96, x_97, x_98, x_99);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
x_110 = l_Lean_Expr_appFn_x21(x_2);
lean_inc(x_99);
lean_inc_ref(x_98);
lean_inc(x_97);
lean_inc_ref(x_96);
x_111 = l_Lean_Meta_mkCongrArg(x_110, x_109, x_96, x_97, x_98, x_99);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
lean_inc(x_99);
lean_inc_ref(x_98);
lean_inc(x_97);
lean_inc_ref(x_96);
lean_inc(x_104);
lean_inc_ref(x_2);
x_113 = l_Lean_Meta_mkEq(x_2, x_104, x_96, x_97, x_98, x_99);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
x_115 = l_Lean_Meta_mkExpectedPropHint(x_112, x_114);
x_116 = 0;
x_117 = l_Lean_Meta_Grind_pushEqCore___redArg(x_2, x_104, x_115, x_116, x_92, x_94, x_96, x_97, x_98, x_99);
lean_dec_ref(x_94);
lean_dec(x_92);
return x_117;
}
else
{
uint8_t x_118; 
lean_dec(x_112);
lean_dec(x_104);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_94);
lean_dec(x_92);
lean_dec_ref(x_2);
x_118 = !lean_is_exclusive(x_113);
if (x_118 == 0)
{
return x_113;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_113, 0);
lean_inc(x_119);
lean_dec(x_113);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_104);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_94);
lean_dec(x_92);
lean_dec_ref(x_2);
x_121 = !lean_is_exclusive(x_111);
if (x_121 == 0)
{
return x_111;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_111, 0);
lean_inc(x_122);
lean_dec(x_111);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_104);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_94);
lean_dec(x_92);
lean_dec_ref(x_2);
x_124 = !lean_is_exclusive(x_108);
if (x_124 == 0)
{
return x_108;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_108, 0);
lean_inc(x_125);
lean_dec(x_108);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
else
{
lean_dec(x_104);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec_ref(x_2);
return x_107;
}
}
else
{
uint8_t x_127; 
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec_ref(x_2);
x_127 = !lean_is_exclusive(x_103);
if (x_127 == 0)
{
return x_103;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_103, 0);
lean_inc(x_128);
lean_dec(x_103);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
}
else
{
lean_object* x_199; 
lean_dec(x_90);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_199 = lean_box(0);
lean_ctor_set(x_88, 0, x_199);
return x_88;
}
}
else
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_88, 0);
lean_inc(x_200);
lean_dec(x_88);
if (lean_obj_tag(x_200) == 1)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec_ref(x_200);
if (x_44 == 0)
{
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
x_202 = x_6;
x_203 = x_7;
x_204 = x_8;
x_205 = x_9;
x_206 = x_10;
x_207 = x_11;
x_208 = x_12;
x_209 = x_13;
x_210 = lean_box(0);
goto block_240;
}
else
{
lean_object* x_241; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_42);
lean_inc(x_38);
x_241 = l_Lean_Meta_Grind_hasSameType(x_38, x_42, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; uint8_t x_243; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
lean_dec_ref(x_241);
x_243 = lean_unbox(x_242);
lean_dec(x_242);
if (x_243 == 0)
{
lean_object* x_244; 
lean_dec(x_201);
lean_dec_ref(x_2);
x_244 = l_Lean_Meta_Grind_getGeneration___redArg(x_38, x_6);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
lean_dec_ref(x_244);
x_246 = l_Lean_Meta_Grind_getGeneration___redArg(x_42, x_6);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; uint8_t x_285; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_dec_ref(x_246);
x_285 = lean_nat_dec_le(x_245, x_247);
if (x_285 == 0)
{
lean_dec(x_247);
x_248 = x_245;
goto block_284;
}
else
{
lean_dec(x_245);
x_248 = x_247;
goto block_284;
}
block_284:
{
lean_object* x_249; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_38);
x_249 = lean_infer_type(x_38, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_dec_ref(x_249);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_251 = l_Lean_Meta_whnfD(x_250, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
lean_dec_ref(x_251);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_42);
x_253 = lean_infer_type(x_42, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_255 = l_Lean_Meta_whnfD(x_254, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 x_257 = x_255;
} else {
 lean_dec_ref(x_255);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_29, 0);
lean_inc(x_258);
lean_dec_ref(x_29);
lean_inc(x_33);
x_259 = l_Lean_Expr_isAppOfArity(x_252, x_258, x_33);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; 
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_252);
lean_dec(x_248);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_23);
x_260 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3;
x_261 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_260, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_261;
}
else
{
uint8_t x_262; 
x_262 = l_Lean_Expr_isAppOfArity(x_256, x_258, x_33);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_258);
lean_dec(x_256);
lean_dec(x_252);
lean_dec(x_248);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_263 = lean_box(0);
if (lean_is_scalar(x_257)) {
 x_264 = lean_alloc_ctor(0, 1, 0);
} else {
 x_264 = x_257;
}
lean_ctor_set(x_264, 0, x_263);
return x_264;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
lean_dec(x_257);
x_265 = lean_st_ref_get(x_13);
x_266 = lean_ctor_get(x_265, 0);
lean_inc_ref(x_266);
lean_dec(x_265);
x_267 = l_Lean_Expr_getAppFn(x_252);
x_268 = l_Lean_Expr_constLevels_x21(x_267);
lean_dec_ref(x_267);
x_269 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_258);
x_270 = l_Lean_Environment_containsOnBranch(x_266, x_269);
if (x_270 == 0)
{
lean_object* x_271; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_269);
x_271 = l_Lean_executeReservedNameAction(x_269, x_12, x_13);
if (lean_obj_tag(x_271) == 0)
{
lean_dec_ref(x_271);
x_45 = x_269;
x_46 = x_268;
x_47 = x_256;
x_48 = x_252;
x_49 = x_248;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_11;
x_56 = x_12;
x_57 = x_13;
x_58 = lean_box(0);
goto block_86;
}
else
{
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_256);
lean_dec(x_252);
lean_dec(x_248);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_271;
}
}
else
{
x_45 = x_269;
x_46 = x_268;
x_47 = x_256;
x_48 = x_252;
x_49 = x_248;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_11;
x_56 = x_12;
x_57 = x_13;
x_58 = lean_box(0);
goto block_86;
}
}
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_252);
lean_dec(x_248);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_272 = lean_ctor_get(x_255, 0);
lean_inc(x_272);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 x_273 = x_255;
} else {
 lean_dec_ref(x_255);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 1, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_252);
lean_dec(x_248);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_275 = lean_ctor_get(x_253, 0);
lean_inc(x_275);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_276 = x_253;
} else {
 lean_dec_ref(x_253);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 1, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_275);
return x_277;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_248);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_278 = lean_ctor_get(x_251, 0);
lean_inc(x_278);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 x_279 = x_251;
} else {
 lean_dec_ref(x_251);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 1, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_278);
return x_280;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_248);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_281 = lean_ctor_get(x_249, 0);
lean_inc(x_281);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 x_282 = x_249;
} else {
 lean_dec_ref(x_249);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(1, 1, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_281);
return x_283;
}
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_245);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_286 = lean_ctor_get(x_246, 0);
lean_inc(x_286);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 x_287 = x_246;
} else {
 lean_dec_ref(x_246);
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
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_289 = lean_ctor_get(x_244, 0);
lean_inc(x_289);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 x_290 = x_244;
} else {
 lean_dec_ref(x_244);
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
else
{
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
x_202 = x_6;
x_203 = x_7;
x_204 = x_8;
x_205 = x_9;
x_206 = x_10;
x_207 = x_11;
x_208 = x_12;
x_209 = x_13;
x_210 = lean_box(0);
goto block_240;
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_201);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_292 = lean_ctor_get(x_241, 0);
lean_inc(x_292);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 x_293 = x_241;
} else {
 lean_dec_ref(x_241);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 1, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_292);
return x_294;
}
}
block_240:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_201, 2);
lean_inc(x_211);
lean_dec(x_201);
x_212 = l_Lean_mkNatLit(x_211);
x_213 = l_Lean_Meta_Grind_shareCommon___redArg(x_212, x_205);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
lean_dec_ref(x_213);
x_215 = lean_unsigned_to_nat(0u);
x_216 = lean_box(0);
lean_inc(x_209);
lean_inc_ref(x_208);
lean_inc(x_207);
lean_inc_ref(x_206);
lean_inc(x_205);
lean_inc_ref(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_214);
x_217 = lean_grind_internalize(x_214, x_215, x_216, x_202, x_203, x_204, x_205, x_206, x_207, x_208, x_209);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; 
lean_dec_ref(x_217);
lean_inc(x_209);
lean_inc_ref(x_208);
lean_inc(x_207);
lean_inc_ref(x_206);
lean_inc_ref(x_204);
lean_inc(x_202);
x_218 = lean_grind_mk_eq_proof(x_38, x_42, x_202, x_203, x_204, x_205, x_206, x_207, x_208, x_209);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
lean_dec_ref(x_218);
x_220 = l_Lean_Expr_appFn_x21(x_2);
lean_inc(x_209);
lean_inc_ref(x_208);
lean_inc(x_207);
lean_inc_ref(x_206);
x_221 = l_Lean_Meta_mkCongrArg(x_220, x_219, x_206, x_207, x_208, x_209);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_dec_ref(x_221);
lean_inc(x_209);
lean_inc_ref(x_208);
lean_inc(x_207);
lean_inc_ref(x_206);
lean_inc(x_214);
lean_inc_ref(x_2);
x_223 = l_Lean_Meta_mkEq(x_2, x_214, x_206, x_207, x_208, x_209);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
lean_dec_ref(x_223);
x_225 = l_Lean_Meta_mkExpectedPropHint(x_222, x_224);
x_226 = 0;
x_227 = l_Lean_Meta_Grind_pushEqCore___redArg(x_2, x_214, x_225, x_226, x_202, x_204, x_206, x_207, x_208, x_209);
lean_dec_ref(x_204);
lean_dec(x_202);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_222);
lean_dec(x_214);
lean_dec(x_209);
lean_dec_ref(x_208);
lean_dec(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_204);
lean_dec(x_202);
lean_dec_ref(x_2);
x_228 = lean_ctor_get(x_223, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 x_229 = x_223;
} else {
 lean_dec_ref(x_223);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_228);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_214);
lean_dec(x_209);
lean_dec_ref(x_208);
lean_dec(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_204);
lean_dec(x_202);
lean_dec_ref(x_2);
x_231 = lean_ctor_get(x_221, 0);
lean_inc(x_231);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 x_232 = x_221;
} else {
 lean_dec_ref(x_221);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 1, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_231);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_214);
lean_dec(x_209);
lean_dec_ref(x_208);
lean_dec(x_207);
lean_dec_ref(x_206);
lean_dec_ref(x_204);
lean_dec(x_202);
lean_dec_ref(x_2);
x_234 = lean_ctor_get(x_218, 0);
lean_inc(x_234);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 x_235 = x_218;
} else {
 lean_dec_ref(x_218);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 1, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_234);
return x_236;
}
}
else
{
lean_dec(x_214);
lean_dec(x_209);
lean_dec_ref(x_208);
lean_dec(x_207);
lean_dec_ref(x_206);
lean_dec(x_205);
lean_dec_ref(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec_ref(x_2);
return x_217;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_209);
lean_dec_ref(x_208);
lean_dec(x_207);
lean_dec_ref(x_206);
lean_dec(x_205);
lean_dec_ref(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec_ref(x_2);
x_237 = lean_ctor_get(x_213, 0);
lean_inc(x_237);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 x_238 = x_213;
} else {
 lean_dec_ref(x_213);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 1, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_237);
return x_239;
}
}
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_200);
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_295 = lean_box(0);
x_296 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_296, 0, x_295);
return x_296;
}
}
}
else
{
uint8_t x_297; 
lean_dec_ref(x_42);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_297 = !lean_is_exclusive(x_88);
if (x_297 == 0)
{
return x_88;
}
else
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_88, 0);
lean_inc(x_298);
lean_dec(x_88);
x_299 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_299, 0, x_298);
return x_299;
}
}
}
block_86:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_inc(x_45);
x_59 = l_Lean_mkConst(x_45, x_46);
x_60 = l_Lean_Meta_Grind_propagateCtorIdxUp___closed__0;
x_61 = l_Lean_Expr_getAppNumArgs(x_48);
lean_inc(x_61);
x_62 = lean_mk_array(x_61, x_60);
x_63 = lean_nat_sub(x_61, x_34);
lean_dec(x_61);
x_64 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_48, x_62, x_63);
x_65 = l_Lean_mkAppN(x_59, x_64);
lean_dec_ref(x_64);
x_66 = l_Lean_Expr_app___override(x_65, x_38);
x_67 = l_Lean_Expr_getAppNumArgs(x_47);
lean_inc(x_67);
x_68 = lean_mk_array(x_67, x_60);
x_69 = lean_nat_sub(x_67, x_34);
lean_dec(x_67);
x_70 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_47, x_68, x_69);
x_71 = l_Lean_mkAppN(x_66, x_70);
lean_dec_ref(x_70);
x_72 = l_Lean_Expr_app___override(x_71, x_42);
lean_inc(x_57);
lean_inc_ref(x_56);
lean_inc(x_55);
lean_inc_ref(x_54);
lean_inc_ref(x_72);
x_73 = lean_infer_type(x_72, x_54, x_55, x_56, x_57);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
if (lean_is_scalar(x_28)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_28;
 lean_ctor_set_tag(x_75, 0);
}
lean_ctor_set(x_75, 0, x_45);
if (lean_is_scalar(x_23)) {
 x_76 = lean_alloc_ctor(7, 1, 0);
} else {
 x_76 = x_23;
 lean_ctor_set_tag(x_76, 7);
}
lean_ctor_set(x_76, 0, x_75);
x_77 = l_Lean_Meta_Grind_addNewRawFact(x_72, x_74, x_49, x_76, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec(x_50);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
x_80 = lean_box(0);
lean_ctor_set(x_77, 0, x_80);
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_77);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
else
{
return x_77;
}
}
else
{
uint8_t x_83; 
lean_dec_ref(x_72);
lean_dec(x_57);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_45);
lean_dec(x_28);
lean_dec(x_23);
x_83 = !lean_is_exclusive(x_73);
if (x_83 == 0)
{
return x_73;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_73, 0);
lean_inc(x_84);
lean_dec(x_73);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
}
else
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_300 = lean_ctor_get(x_39, 0);
lean_inc(x_300);
lean_dec(x_39);
x_301 = lean_ctor_get(x_300, 0);
lean_inc_ref(x_301);
x_302 = lean_ctor_get_uint8(x_300, sizeof(void*)*11 + 2);
x_303 = lean_ctor_get_uint8(x_300, sizeof(void*)*11 + 4);
lean_dec(x_300);
if (x_302 == 0)
{
lean_object* x_344; lean_object* x_345; 
lean_dec_ref(x_301);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_344 = lean_box(0);
x_345 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_345, 0, x_344);
return x_345;
}
else
{
lean_object* x_346; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_301);
x_346 = l_Lean_Meta_isConstructorApp_x3f(x_301, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 x_348 = x_346;
} else {
 lean_dec_ref(x_346);
 x_348 = lean_box(0);
}
if (lean_obj_tag(x_347) == 1)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_dec(x_348);
x_349 = lean_ctor_get(x_347, 0);
lean_inc(x_349);
lean_dec_ref(x_347);
if (x_303 == 0)
{
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
x_350 = x_6;
x_351 = x_7;
x_352 = x_8;
x_353 = x_9;
x_354 = x_10;
x_355 = x_11;
x_356 = x_12;
x_357 = x_13;
x_358 = lean_box(0);
goto block_388;
}
else
{
lean_object* x_389; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_301);
lean_inc(x_38);
x_389 = l_Lean_Meta_Grind_hasSameType(x_38, x_301, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; uint8_t x_391; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
lean_dec_ref(x_389);
x_391 = lean_unbox(x_390);
lean_dec(x_390);
if (x_391 == 0)
{
lean_object* x_392; 
lean_dec(x_349);
lean_dec_ref(x_2);
x_392 = l_Lean_Meta_Grind_getGeneration___redArg(x_38, x_6);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
lean_dec_ref(x_392);
x_394 = l_Lean_Meta_Grind_getGeneration___redArg(x_301, x_6);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; uint8_t x_433; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
lean_dec_ref(x_394);
x_433 = lean_nat_dec_le(x_393, x_395);
if (x_433 == 0)
{
lean_dec(x_395);
x_396 = x_393;
goto block_432;
}
else
{
lean_dec(x_393);
x_396 = x_395;
goto block_432;
}
block_432:
{
lean_object* x_397; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_38);
x_397 = lean_infer_type(x_38, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; 
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
lean_dec_ref(x_397);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_399 = l_Lean_Meta_whnfD(x_398, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; lean_object* x_401; 
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
lean_dec_ref(x_399);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_301);
x_401 = lean_infer_type(x_301, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
lean_dec_ref(x_401);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_403 = l_Lean_Meta_whnfD(x_402, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 x_405 = x_403;
} else {
 lean_dec_ref(x_403);
 x_405 = lean_box(0);
}
x_406 = lean_ctor_get(x_29, 0);
lean_inc(x_406);
lean_dec_ref(x_29);
lean_inc(x_33);
x_407 = l_Lean_Expr_isAppOfArity(x_400, x_406, x_33);
if (x_407 == 0)
{
lean_object* x_408; lean_object* x_409; 
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_400);
lean_dec(x_396);
lean_dec_ref(x_301);
lean_dec(x_38);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_23);
x_408 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3;
x_409 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_408, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_409;
}
else
{
uint8_t x_410; 
x_410 = l_Lean_Expr_isAppOfArity(x_404, x_406, x_33);
if (x_410 == 0)
{
lean_object* x_411; lean_object* x_412; 
lean_dec(x_406);
lean_dec(x_404);
lean_dec(x_400);
lean_dec(x_396);
lean_dec_ref(x_301);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_411 = lean_box(0);
if (lean_is_scalar(x_405)) {
 x_412 = lean_alloc_ctor(0, 1, 0);
} else {
 x_412 = x_405;
}
lean_ctor_set(x_412, 0, x_411);
return x_412;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
lean_dec(x_405);
x_413 = lean_st_ref_get(x_13);
x_414 = lean_ctor_get(x_413, 0);
lean_inc_ref(x_414);
lean_dec(x_413);
x_415 = l_Lean_Expr_getAppFn(x_400);
x_416 = l_Lean_Expr_constLevels_x21(x_415);
lean_dec_ref(x_415);
x_417 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_406);
x_418 = l_Lean_Environment_containsOnBranch(x_414, x_417);
if (x_418 == 0)
{
lean_object* x_419; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_417);
x_419 = l_Lean_executeReservedNameAction(x_417, x_12, x_13);
if (lean_obj_tag(x_419) == 0)
{
lean_dec_ref(x_419);
x_304 = x_417;
x_305 = x_416;
x_306 = x_404;
x_307 = x_400;
x_308 = x_396;
x_309 = x_6;
x_310 = x_7;
x_311 = x_8;
x_312 = x_9;
x_313 = x_10;
x_314 = x_11;
x_315 = x_12;
x_316 = x_13;
x_317 = lean_box(0);
goto block_343;
}
else
{
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_404);
lean_dec(x_400);
lean_dec(x_396);
lean_dec_ref(x_301);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_419;
}
}
else
{
x_304 = x_417;
x_305 = x_416;
x_306 = x_404;
x_307 = x_400;
x_308 = x_396;
x_309 = x_6;
x_310 = x_7;
x_311 = x_8;
x_312 = x_9;
x_313 = x_10;
x_314 = x_11;
x_315 = x_12;
x_316 = x_13;
x_317 = lean_box(0);
goto block_343;
}
}
}
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_400);
lean_dec(x_396);
lean_dec_ref(x_301);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_420 = lean_ctor_get(x_403, 0);
lean_inc(x_420);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 x_421 = x_403;
} else {
 lean_dec_ref(x_403);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(1, 1, 0);
} else {
 x_422 = x_421;
}
lean_ctor_set(x_422, 0, x_420);
return x_422;
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_400);
lean_dec(x_396);
lean_dec_ref(x_301);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_423 = lean_ctor_get(x_401, 0);
lean_inc(x_423);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 x_424 = x_401;
} else {
 lean_dec_ref(x_401);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 1, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_423);
return x_425;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_396);
lean_dec_ref(x_301);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_426 = lean_ctor_get(x_399, 0);
lean_inc(x_426);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 x_427 = x_399;
} else {
 lean_dec_ref(x_399);
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
lean_dec(x_396);
lean_dec_ref(x_301);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_429 = lean_ctor_get(x_397, 0);
lean_inc(x_429);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 x_430 = x_397;
} else {
 lean_dec_ref(x_397);
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
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_393);
lean_dec_ref(x_301);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_434 = lean_ctor_get(x_394, 0);
lean_inc(x_434);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 x_435 = x_394;
} else {
 lean_dec_ref(x_394);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_435)) {
 x_436 = lean_alloc_ctor(1, 1, 0);
} else {
 x_436 = x_435;
}
lean_ctor_set(x_436, 0, x_434);
return x_436;
}
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec_ref(x_301);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_437 = lean_ctor_get(x_392, 0);
lean_inc(x_437);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 x_438 = x_392;
} else {
 lean_dec_ref(x_392);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 1, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_437);
return x_439;
}
}
else
{
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
x_350 = x_6;
x_351 = x_7;
x_352 = x_8;
x_353 = x_9;
x_354 = x_10;
x_355 = x_11;
x_356 = x_12;
x_357 = x_13;
x_358 = lean_box(0);
goto block_388;
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_349);
lean_dec_ref(x_301);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_440 = lean_ctor_get(x_389, 0);
lean_inc(x_440);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 x_441 = x_389;
} else {
 lean_dec_ref(x_389);
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
block_388:
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_349, 2);
lean_inc(x_359);
lean_dec(x_349);
x_360 = l_Lean_mkNatLit(x_359);
x_361 = l_Lean_Meta_Grind_shareCommon___redArg(x_360, x_353);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
lean_dec_ref(x_361);
x_363 = lean_unsigned_to_nat(0u);
x_364 = lean_box(0);
lean_inc(x_357);
lean_inc_ref(x_356);
lean_inc(x_355);
lean_inc_ref(x_354);
lean_inc(x_353);
lean_inc_ref(x_352);
lean_inc(x_351);
lean_inc(x_350);
lean_inc(x_362);
x_365 = lean_grind_internalize(x_362, x_363, x_364, x_350, x_351, x_352, x_353, x_354, x_355, x_356, x_357);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; 
lean_dec_ref(x_365);
lean_inc(x_357);
lean_inc_ref(x_356);
lean_inc(x_355);
lean_inc_ref(x_354);
lean_inc_ref(x_352);
lean_inc(x_350);
x_366 = lean_grind_mk_eq_proof(x_38, x_301, x_350, x_351, x_352, x_353, x_354, x_355, x_356, x_357);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
lean_dec_ref(x_366);
x_368 = l_Lean_Expr_appFn_x21(x_2);
lean_inc(x_357);
lean_inc_ref(x_356);
lean_inc(x_355);
lean_inc_ref(x_354);
x_369 = l_Lean_Meta_mkCongrArg(x_368, x_367, x_354, x_355, x_356, x_357);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
lean_dec_ref(x_369);
lean_inc(x_357);
lean_inc_ref(x_356);
lean_inc(x_355);
lean_inc_ref(x_354);
lean_inc(x_362);
lean_inc_ref(x_2);
x_371 = l_Lean_Meta_mkEq(x_2, x_362, x_354, x_355, x_356, x_357);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; uint8_t x_374; lean_object* x_375; 
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
lean_dec_ref(x_371);
x_373 = l_Lean_Meta_mkExpectedPropHint(x_370, x_372);
x_374 = 0;
x_375 = l_Lean_Meta_Grind_pushEqCore___redArg(x_2, x_362, x_373, x_374, x_350, x_352, x_354, x_355, x_356, x_357);
lean_dec_ref(x_352);
lean_dec(x_350);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_370);
lean_dec(x_362);
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec(x_355);
lean_dec_ref(x_354);
lean_dec_ref(x_352);
lean_dec(x_350);
lean_dec_ref(x_2);
x_376 = lean_ctor_get(x_371, 0);
lean_inc(x_376);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 x_377 = x_371;
} else {
 lean_dec_ref(x_371);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(1, 1, 0);
} else {
 x_378 = x_377;
}
lean_ctor_set(x_378, 0, x_376);
return x_378;
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_362);
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec(x_355);
lean_dec_ref(x_354);
lean_dec_ref(x_352);
lean_dec(x_350);
lean_dec_ref(x_2);
x_379 = lean_ctor_get(x_369, 0);
lean_inc(x_379);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 x_380 = x_369;
} else {
 lean_dec_ref(x_369);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(1, 1, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_379);
return x_381;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_362);
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec(x_355);
lean_dec_ref(x_354);
lean_dec_ref(x_352);
lean_dec(x_350);
lean_dec_ref(x_2);
x_382 = lean_ctor_get(x_366, 0);
lean_inc(x_382);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 x_383 = x_366;
} else {
 lean_dec_ref(x_366);
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
lean_dec(x_362);
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec(x_355);
lean_dec_ref(x_354);
lean_dec(x_353);
lean_dec_ref(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec_ref(x_301);
lean_dec(x_38);
lean_dec_ref(x_2);
return x_365;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec(x_355);
lean_dec_ref(x_354);
lean_dec(x_353);
lean_dec_ref(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec_ref(x_301);
lean_dec(x_38);
lean_dec_ref(x_2);
x_385 = lean_ctor_get(x_361, 0);
lean_inc(x_385);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 x_386 = x_361;
} else {
 lean_dec_ref(x_361);
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
}
else
{
lean_object* x_443; lean_object* x_444; 
lean_dec(x_347);
lean_dec_ref(x_301);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_443 = lean_box(0);
if (lean_is_scalar(x_348)) {
 x_444 = lean_alloc_ctor(0, 1, 0);
} else {
 x_444 = x_348;
}
lean_ctor_set(x_444, 0, x_443);
return x_444;
}
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_dec_ref(x_301);
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_445 = lean_ctor_get(x_346, 0);
lean_inc(x_445);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 x_446 = x_346;
} else {
 lean_dec_ref(x_346);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(1, 1, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_445);
return x_447;
}
}
block_343:
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_inc(x_304);
x_318 = l_Lean_mkConst(x_304, x_305);
x_319 = l_Lean_Meta_Grind_propagateCtorIdxUp___closed__0;
x_320 = l_Lean_Expr_getAppNumArgs(x_307);
lean_inc(x_320);
x_321 = lean_mk_array(x_320, x_319);
x_322 = lean_nat_sub(x_320, x_34);
lean_dec(x_320);
x_323 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_307, x_321, x_322);
x_324 = l_Lean_mkAppN(x_318, x_323);
lean_dec_ref(x_323);
x_325 = l_Lean_Expr_app___override(x_324, x_38);
x_326 = l_Lean_Expr_getAppNumArgs(x_306);
lean_inc(x_326);
x_327 = lean_mk_array(x_326, x_319);
x_328 = lean_nat_sub(x_326, x_34);
lean_dec(x_326);
x_329 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_306, x_327, x_328);
x_330 = l_Lean_mkAppN(x_325, x_329);
lean_dec_ref(x_329);
x_331 = l_Lean_Expr_app___override(x_330, x_301);
lean_inc(x_316);
lean_inc_ref(x_315);
lean_inc(x_314);
lean_inc_ref(x_313);
lean_inc_ref(x_331);
x_332 = lean_infer_type(x_331, x_313, x_314, x_315, x_316);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
lean_dec_ref(x_332);
if (lean_is_scalar(x_28)) {
 x_334 = lean_alloc_ctor(0, 1, 0);
} else {
 x_334 = x_28;
 lean_ctor_set_tag(x_334, 0);
}
lean_ctor_set(x_334, 0, x_304);
if (lean_is_scalar(x_23)) {
 x_335 = lean_alloc_ctor(7, 1, 0);
} else {
 x_335 = x_23;
 lean_ctor_set_tag(x_335, 7);
}
lean_ctor_set(x_335, 0, x_334);
x_336 = l_Lean_Meta_Grind_addNewRawFact(x_331, x_333, x_308, x_335, x_309, x_310, x_311, x_312, x_313, x_314, x_315, x_316);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec(x_309);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 x_337 = x_336;
} else {
 lean_dec_ref(x_336);
 x_337 = lean_box(0);
}
x_338 = lean_box(0);
if (lean_is_scalar(x_337)) {
 x_339 = lean_alloc_ctor(0, 1, 0);
} else {
 x_339 = x_337;
}
lean_ctor_set(x_339, 0, x_338);
return x_339;
}
else
{
return x_336;
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec_ref(x_331);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_308);
lean_dec(x_304);
lean_dec(x_28);
lean_dec(x_23);
x_340 = lean_ctor_get(x_332, 0);
lean_inc(x_340);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 x_341 = x_332;
} else {
 lean_dec_ref(x_332);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(1, 1, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_340);
return x_342;
}
}
}
}
else
{
uint8_t x_448; 
lean_dec(x_38);
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_448 = !lean_is_exclusive(x_39);
if (x_448 == 0)
{
return x_39;
}
else
{
lean_object* x_449; lean_object* x_450; 
x_449 = lean_ctor_get(x_39, 0);
lean_inc(x_449);
lean_dec(x_39);
x_450 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_450, 0, x_449);
return x_450;
}
}
}
}
else
{
lean_object* x_451; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_451 = lean_box(0);
lean_ctor_set(x_24, 0, x_451);
return x_24;
}
}
else
{
lean_object* x_452; 
x_452 = lean_ctor_get(x_24, 0);
lean_inc(x_452);
lean_dec(x_24);
if (lean_obj_tag(x_452) == 1)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; 
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 x_454 = x_452;
} else {
 lean_dec_ref(x_452);
 x_454 = lean_box(0);
}
x_455 = lean_ctor_get(x_453, 0);
lean_inc_ref(x_455);
x_456 = lean_ctor_get(x_453, 1);
lean_inc(x_456);
x_457 = lean_ctor_get(x_453, 2);
lean_inc(x_457);
lean_dec(x_453);
x_458 = lean_array_get_size(x_4);
x_459 = lean_nat_add(x_456, x_457);
lean_dec(x_457);
lean_dec(x_456);
x_460 = lean_unsigned_to_nat(1u);
x_461 = lean_nat_add(x_459, x_460);
x_462 = lean_nat_dec_eq(x_458, x_461);
lean_dec(x_461);
if (x_462 == 0)
{
lean_object* x_463; lean_object* x_464; 
lean_dec(x_459);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_463 = lean_box(0);
x_464 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_464, 0, x_463);
return x_464;
}
else
{
lean_object* x_465; lean_object* x_466; 
x_465 = l_Array_back_x21___redArg(x_1, x_4);
lean_dec_ref(x_4);
lean_inc(x_465);
x_466 = l_Lean_Meta_Grind_getRootENode___redArg(x_465, x_6, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; uint8_t x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 x_468 = x_466;
} else {
 lean_dec_ref(x_466);
 x_468 = lean_box(0);
}
x_469 = lean_ctor_get(x_467, 0);
lean_inc_ref(x_469);
x_470 = lean_ctor_get_uint8(x_467, sizeof(void*)*11 + 2);
x_471 = lean_ctor_get_uint8(x_467, sizeof(void*)*11 + 4);
lean_dec(x_467);
if (x_470 == 0)
{
lean_object* x_512; lean_object* x_513; 
lean_dec_ref(x_469);
lean_dec(x_465);
lean_dec(x_459);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_512 = lean_box(0);
if (lean_is_scalar(x_468)) {
 x_513 = lean_alloc_ctor(0, 1, 0);
} else {
 x_513 = x_468;
}
lean_ctor_set(x_513, 0, x_512);
return x_513;
}
else
{
lean_object* x_514; 
lean_dec(x_468);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_469);
x_514 = l_Lean_Meta_isConstructorApp_x3f(x_469, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_514) == 0)
{
lean_object* x_515; lean_object* x_516; 
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
if (lean_is_exclusive(x_514)) {
 lean_ctor_release(x_514, 0);
 x_516 = x_514;
} else {
 lean_dec_ref(x_514);
 x_516 = lean_box(0);
}
if (lean_obj_tag(x_515) == 1)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
lean_dec(x_516);
x_517 = lean_ctor_get(x_515, 0);
lean_inc(x_517);
lean_dec_ref(x_515);
if (x_471 == 0)
{
lean_dec(x_459);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_23);
x_518 = x_6;
x_519 = x_7;
x_520 = x_8;
x_521 = x_9;
x_522 = x_10;
x_523 = x_11;
x_524 = x_12;
x_525 = x_13;
x_526 = lean_box(0);
goto block_556;
}
else
{
lean_object* x_557; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_469);
lean_inc(x_465);
x_557 = l_Lean_Meta_Grind_hasSameType(x_465, x_469, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; uint8_t x_559; 
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
lean_dec_ref(x_557);
x_559 = lean_unbox(x_558);
lean_dec(x_558);
if (x_559 == 0)
{
lean_object* x_560; 
lean_dec(x_517);
lean_dec_ref(x_2);
x_560 = l_Lean_Meta_Grind_getGeneration___redArg(x_465, x_6);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; lean_object* x_562; 
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
lean_dec_ref(x_560);
x_562 = l_Lean_Meta_Grind_getGeneration___redArg(x_469, x_6);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; lean_object* x_564; uint8_t x_601; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
lean_dec_ref(x_562);
x_601 = lean_nat_dec_le(x_561, x_563);
if (x_601 == 0)
{
lean_dec(x_563);
x_564 = x_561;
goto block_600;
}
else
{
lean_dec(x_561);
x_564 = x_563;
goto block_600;
}
block_600:
{
lean_object* x_565; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_465);
x_565 = lean_infer_type(x_465, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_565) == 0)
{
lean_object* x_566; lean_object* x_567; 
x_566 = lean_ctor_get(x_565, 0);
lean_inc(x_566);
lean_dec_ref(x_565);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_567 = l_Lean_Meta_whnfD(x_566, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_567) == 0)
{
lean_object* x_568; lean_object* x_569; 
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
lean_dec_ref(x_567);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_469);
x_569 = lean_infer_type(x_469, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; 
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
lean_dec_ref(x_569);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_571 = l_Lean_Meta_whnfD(x_570, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; uint8_t x_575; 
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 x_573 = x_571;
} else {
 lean_dec_ref(x_571);
 x_573 = lean_box(0);
}
x_574 = lean_ctor_get(x_455, 0);
lean_inc(x_574);
lean_dec_ref(x_455);
lean_inc(x_459);
x_575 = l_Lean_Expr_isAppOfArity(x_568, x_574, x_459);
if (x_575 == 0)
{
lean_object* x_576; lean_object* x_577; 
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_572);
lean_dec(x_568);
lean_dec(x_564);
lean_dec_ref(x_469);
lean_dec(x_465);
lean_dec(x_459);
lean_dec(x_454);
lean_dec(x_23);
x_576 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3;
x_577 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_576, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_577;
}
else
{
uint8_t x_578; 
x_578 = l_Lean_Expr_isAppOfArity(x_572, x_574, x_459);
if (x_578 == 0)
{
lean_object* x_579; lean_object* x_580; 
lean_dec(x_574);
lean_dec(x_572);
lean_dec(x_568);
lean_dec(x_564);
lean_dec_ref(x_469);
lean_dec(x_465);
lean_dec(x_454);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_579 = lean_box(0);
if (lean_is_scalar(x_573)) {
 x_580 = lean_alloc_ctor(0, 1, 0);
} else {
 x_580 = x_573;
}
lean_ctor_set(x_580, 0, x_579);
return x_580;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; uint8_t x_586; 
lean_dec(x_573);
x_581 = lean_st_ref_get(x_13);
x_582 = lean_ctor_get(x_581, 0);
lean_inc_ref(x_582);
lean_dec(x_581);
x_583 = l_Lean_Expr_getAppFn(x_568);
x_584 = l_Lean_Expr_constLevels_x21(x_583);
lean_dec_ref(x_583);
x_585 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_574);
x_586 = l_Lean_Environment_containsOnBranch(x_582, x_585);
if (x_586 == 0)
{
lean_object* x_587; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_585);
x_587 = l_Lean_executeReservedNameAction(x_585, x_12, x_13);
if (lean_obj_tag(x_587) == 0)
{
lean_dec_ref(x_587);
x_472 = x_585;
x_473 = x_584;
x_474 = x_572;
x_475 = x_568;
x_476 = x_564;
x_477 = x_6;
x_478 = x_7;
x_479 = x_8;
x_480 = x_9;
x_481 = x_10;
x_482 = x_11;
x_483 = x_12;
x_484 = x_13;
x_485 = lean_box(0);
goto block_511;
}
else
{
lean_dec(x_585);
lean_dec(x_584);
lean_dec(x_572);
lean_dec(x_568);
lean_dec(x_564);
lean_dec_ref(x_469);
lean_dec(x_465);
lean_dec(x_454);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_587;
}
}
else
{
x_472 = x_585;
x_473 = x_584;
x_474 = x_572;
x_475 = x_568;
x_476 = x_564;
x_477 = x_6;
x_478 = x_7;
x_479 = x_8;
x_480 = x_9;
x_481 = x_10;
x_482 = x_11;
x_483 = x_12;
x_484 = x_13;
x_485 = lean_box(0);
goto block_511;
}
}
}
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
lean_dec(x_568);
lean_dec(x_564);
lean_dec_ref(x_469);
lean_dec(x_465);
lean_dec(x_459);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_588 = lean_ctor_get(x_571, 0);
lean_inc(x_588);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 x_589 = x_571;
} else {
 lean_dec_ref(x_571);
 x_589 = lean_box(0);
}
if (lean_is_scalar(x_589)) {
 x_590 = lean_alloc_ctor(1, 1, 0);
} else {
 x_590 = x_589;
}
lean_ctor_set(x_590, 0, x_588);
return x_590;
}
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; 
lean_dec(x_568);
lean_dec(x_564);
lean_dec_ref(x_469);
lean_dec(x_465);
lean_dec(x_459);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_591 = lean_ctor_get(x_569, 0);
lean_inc(x_591);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 x_592 = x_569;
} else {
 lean_dec_ref(x_569);
 x_592 = lean_box(0);
}
if (lean_is_scalar(x_592)) {
 x_593 = lean_alloc_ctor(1, 1, 0);
} else {
 x_593 = x_592;
}
lean_ctor_set(x_593, 0, x_591);
return x_593;
}
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; 
lean_dec(x_564);
lean_dec_ref(x_469);
lean_dec(x_465);
lean_dec(x_459);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_594 = lean_ctor_get(x_567, 0);
lean_inc(x_594);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 x_595 = x_567;
} else {
 lean_dec_ref(x_567);
 x_595 = lean_box(0);
}
if (lean_is_scalar(x_595)) {
 x_596 = lean_alloc_ctor(1, 1, 0);
} else {
 x_596 = x_595;
}
lean_ctor_set(x_596, 0, x_594);
return x_596;
}
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_564);
lean_dec_ref(x_469);
lean_dec(x_465);
lean_dec(x_459);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_597 = lean_ctor_get(x_565, 0);
lean_inc(x_597);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 x_598 = x_565;
} else {
 lean_dec_ref(x_565);
 x_598 = lean_box(0);
}
if (lean_is_scalar(x_598)) {
 x_599 = lean_alloc_ctor(1, 1, 0);
} else {
 x_599 = x_598;
}
lean_ctor_set(x_599, 0, x_597);
return x_599;
}
}
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
lean_dec(x_561);
lean_dec_ref(x_469);
lean_dec(x_465);
lean_dec(x_459);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_602 = lean_ctor_get(x_562, 0);
lean_inc(x_602);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 x_603 = x_562;
} else {
 lean_dec_ref(x_562);
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
lean_dec_ref(x_469);
lean_dec(x_465);
lean_dec(x_459);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_605 = lean_ctor_get(x_560, 0);
lean_inc(x_605);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 x_606 = x_560;
} else {
 lean_dec_ref(x_560);
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
lean_dec(x_459);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_23);
x_518 = x_6;
x_519 = x_7;
x_520 = x_8;
x_521 = x_9;
x_522 = x_10;
x_523 = x_11;
x_524 = x_12;
x_525 = x_13;
x_526 = lean_box(0);
goto block_556;
}
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_517);
lean_dec_ref(x_469);
lean_dec(x_465);
lean_dec(x_459);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_608 = lean_ctor_get(x_557, 0);
lean_inc(x_608);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 x_609 = x_557;
} else {
 lean_dec_ref(x_557);
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
block_556:
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_527 = lean_ctor_get(x_517, 2);
lean_inc(x_527);
lean_dec(x_517);
x_528 = l_Lean_mkNatLit(x_527);
x_529 = l_Lean_Meta_Grind_shareCommon___redArg(x_528, x_521);
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
lean_dec_ref(x_529);
x_531 = lean_unsigned_to_nat(0u);
x_532 = lean_box(0);
lean_inc(x_525);
lean_inc_ref(x_524);
lean_inc(x_523);
lean_inc_ref(x_522);
lean_inc(x_521);
lean_inc_ref(x_520);
lean_inc(x_519);
lean_inc(x_518);
lean_inc(x_530);
x_533 = lean_grind_internalize(x_530, x_531, x_532, x_518, x_519, x_520, x_521, x_522, x_523, x_524, x_525);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; 
lean_dec_ref(x_533);
lean_inc(x_525);
lean_inc_ref(x_524);
lean_inc(x_523);
lean_inc_ref(x_522);
lean_inc_ref(x_520);
lean_inc(x_518);
x_534 = lean_grind_mk_eq_proof(x_465, x_469, x_518, x_519, x_520, x_521, x_522, x_523, x_524, x_525);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
lean_dec_ref(x_534);
x_536 = l_Lean_Expr_appFn_x21(x_2);
lean_inc(x_525);
lean_inc_ref(x_524);
lean_inc(x_523);
lean_inc_ref(x_522);
x_537 = l_Lean_Meta_mkCongrArg(x_536, x_535, x_522, x_523, x_524, x_525);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; lean_object* x_539; 
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
lean_dec_ref(x_537);
lean_inc(x_525);
lean_inc_ref(x_524);
lean_inc(x_523);
lean_inc_ref(x_522);
lean_inc(x_530);
lean_inc_ref(x_2);
x_539 = l_Lean_Meta_mkEq(x_2, x_530, x_522, x_523, x_524, x_525);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; lean_object* x_541; uint8_t x_542; lean_object* x_543; 
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
lean_dec_ref(x_539);
x_541 = l_Lean_Meta_mkExpectedPropHint(x_538, x_540);
x_542 = 0;
x_543 = l_Lean_Meta_Grind_pushEqCore___redArg(x_2, x_530, x_541, x_542, x_518, x_520, x_522, x_523, x_524, x_525);
lean_dec_ref(x_520);
lean_dec(x_518);
return x_543;
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; 
lean_dec(x_538);
lean_dec(x_530);
lean_dec(x_525);
lean_dec_ref(x_524);
lean_dec(x_523);
lean_dec_ref(x_522);
lean_dec_ref(x_520);
lean_dec(x_518);
lean_dec_ref(x_2);
x_544 = lean_ctor_get(x_539, 0);
lean_inc(x_544);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 x_545 = x_539;
} else {
 lean_dec_ref(x_539);
 x_545 = lean_box(0);
}
if (lean_is_scalar(x_545)) {
 x_546 = lean_alloc_ctor(1, 1, 0);
} else {
 x_546 = x_545;
}
lean_ctor_set(x_546, 0, x_544);
return x_546;
}
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec(x_530);
lean_dec(x_525);
lean_dec_ref(x_524);
lean_dec(x_523);
lean_dec_ref(x_522);
lean_dec_ref(x_520);
lean_dec(x_518);
lean_dec_ref(x_2);
x_547 = lean_ctor_get(x_537, 0);
lean_inc(x_547);
if (lean_is_exclusive(x_537)) {
 lean_ctor_release(x_537, 0);
 x_548 = x_537;
} else {
 lean_dec_ref(x_537);
 x_548 = lean_box(0);
}
if (lean_is_scalar(x_548)) {
 x_549 = lean_alloc_ctor(1, 1, 0);
} else {
 x_549 = x_548;
}
lean_ctor_set(x_549, 0, x_547);
return x_549;
}
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_530);
lean_dec(x_525);
lean_dec_ref(x_524);
lean_dec(x_523);
lean_dec_ref(x_522);
lean_dec_ref(x_520);
lean_dec(x_518);
lean_dec_ref(x_2);
x_550 = lean_ctor_get(x_534, 0);
lean_inc(x_550);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 x_551 = x_534;
} else {
 lean_dec_ref(x_534);
 x_551 = lean_box(0);
}
if (lean_is_scalar(x_551)) {
 x_552 = lean_alloc_ctor(1, 1, 0);
} else {
 x_552 = x_551;
}
lean_ctor_set(x_552, 0, x_550);
return x_552;
}
}
else
{
lean_dec(x_530);
lean_dec(x_525);
lean_dec_ref(x_524);
lean_dec(x_523);
lean_dec_ref(x_522);
lean_dec(x_521);
lean_dec_ref(x_520);
lean_dec(x_519);
lean_dec(x_518);
lean_dec_ref(x_469);
lean_dec(x_465);
lean_dec_ref(x_2);
return x_533;
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
lean_dec(x_525);
lean_dec_ref(x_524);
lean_dec(x_523);
lean_dec_ref(x_522);
lean_dec(x_521);
lean_dec_ref(x_520);
lean_dec(x_519);
lean_dec(x_518);
lean_dec_ref(x_469);
lean_dec(x_465);
lean_dec_ref(x_2);
x_553 = lean_ctor_get(x_529, 0);
lean_inc(x_553);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 x_554 = x_529;
} else {
 lean_dec_ref(x_529);
 x_554 = lean_box(0);
}
if (lean_is_scalar(x_554)) {
 x_555 = lean_alloc_ctor(1, 1, 0);
} else {
 x_555 = x_554;
}
lean_ctor_set(x_555, 0, x_553);
return x_555;
}
}
}
else
{
lean_object* x_611; lean_object* x_612; 
lean_dec(x_515);
lean_dec_ref(x_469);
lean_dec(x_465);
lean_dec(x_459);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_611 = lean_box(0);
if (lean_is_scalar(x_516)) {
 x_612 = lean_alloc_ctor(0, 1, 0);
} else {
 x_612 = x_516;
}
lean_ctor_set(x_612, 0, x_611);
return x_612;
}
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
lean_dec_ref(x_469);
lean_dec(x_465);
lean_dec(x_459);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_613 = lean_ctor_get(x_514, 0);
lean_inc(x_613);
if (lean_is_exclusive(x_514)) {
 lean_ctor_release(x_514, 0);
 x_614 = x_514;
} else {
 lean_dec_ref(x_514);
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
block_511:
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_inc(x_472);
x_486 = l_Lean_mkConst(x_472, x_473);
x_487 = l_Lean_Meta_Grind_propagateCtorIdxUp___closed__0;
x_488 = l_Lean_Expr_getAppNumArgs(x_475);
lean_inc(x_488);
x_489 = lean_mk_array(x_488, x_487);
x_490 = lean_nat_sub(x_488, x_460);
lean_dec(x_488);
x_491 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_475, x_489, x_490);
x_492 = l_Lean_mkAppN(x_486, x_491);
lean_dec_ref(x_491);
x_493 = l_Lean_Expr_app___override(x_492, x_465);
x_494 = l_Lean_Expr_getAppNumArgs(x_474);
lean_inc(x_494);
x_495 = lean_mk_array(x_494, x_487);
x_496 = lean_nat_sub(x_494, x_460);
lean_dec(x_494);
x_497 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_474, x_495, x_496);
x_498 = l_Lean_mkAppN(x_493, x_497);
lean_dec_ref(x_497);
x_499 = l_Lean_Expr_app___override(x_498, x_469);
lean_inc(x_484);
lean_inc_ref(x_483);
lean_inc(x_482);
lean_inc_ref(x_481);
lean_inc_ref(x_499);
x_500 = lean_infer_type(x_499, x_481, x_482, x_483, x_484);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
lean_dec_ref(x_500);
if (lean_is_scalar(x_454)) {
 x_502 = lean_alloc_ctor(0, 1, 0);
} else {
 x_502 = x_454;
 lean_ctor_set_tag(x_502, 0);
}
lean_ctor_set(x_502, 0, x_472);
if (lean_is_scalar(x_23)) {
 x_503 = lean_alloc_ctor(7, 1, 0);
} else {
 x_503 = x_23;
 lean_ctor_set_tag(x_503, 7);
}
lean_ctor_set(x_503, 0, x_502);
x_504 = l_Lean_Meta_Grind_addNewRawFact(x_499, x_501, x_476, x_503, x_477, x_478, x_479, x_480, x_481, x_482, x_483, x_484);
lean_dec(x_480);
lean_dec_ref(x_479);
lean_dec(x_478);
lean_dec(x_477);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; 
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 x_505 = x_504;
} else {
 lean_dec_ref(x_504);
 x_505 = lean_box(0);
}
x_506 = lean_box(0);
if (lean_is_scalar(x_505)) {
 x_507 = lean_alloc_ctor(0, 1, 0);
} else {
 x_507 = x_505;
}
lean_ctor_set(x_507, 0, x_506);
return x_507;
}
else
{
return x_504;
}
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec_ref(x_499);
lean_dec(x_484);
lean_dec_ref(x_483);
lean_dec(x_482);
lean_dec_ref(x_481);
lean_dec(x_480);
lean_dec_ref(x_479);
lean_dec(x_478);
lean_dec(x_477);
lean_dec(x_476);
lean_dec(x_472);
lean_dec(x_454);
lean_dec(x_23);
x_508 = lean_ctor_get(x_500, 0);
lean_inc(x_508);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 x_509 = x_500;
} else {
 lean_dec_ref(x_500);
 x_509 = lean_box(0);
}
if (lean_is_scalar(x_509)) {
 x_510 = lean_alloc_ctor(1, 1, 0);
} else {
 x_510 = x_509;
}
lean_ctor_set(x_510, 0, x_508);
return x_510;
}
}
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
lean_dec(x_465);
lean_dec(x_459);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_616 = lean_ctor_get(x_466, 0);
lean_inc(x_616);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 x_617 = x_466;
} else {
 lean_dec_ref(x_466);
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
}
else
{
lean_object* x_619; lean_object* x_620; 
lean_dec(x_452);
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_619 = lean_box(0);
x_620 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_620, 0, x_619);
return x_620;
}
}
}
else
{
uint8_t x_621; 
lean_dec(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_621 = !lean_is_exclusive(x_24);
if (x_621 == 0)
{
return x_24;
}
else
{
lean_object* x_622; lean_object* x_623; 
x_622 = lean_ctor_get(x_24, 0);
lean_inc(x_622);
lean_dec(x_24);
x_623 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_623, 0, x_622);
return x_623;
}
}
}
else
{
lean_object* x_624; lean_object* x_625; 
lean_dec(x_21);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_624 = lean_box(0);
x_625 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_625, 0, x_624);
return x_625;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = l_Lean_instInhabitedExpr;
x_12 = l_Lean_Meta_Grind_propagateCtorIdxUp___closed__0;
x_13 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_13);
x_14 = lean_mk_array(x_13, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_13, x_15);
lean_dec(x_13);
lean_inc_ref(x_1);
x_17 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(x_11, x_1, x_1, x_14, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_propagateCtorIdxUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
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
l_Lean_Meta_Grind_propagateCtorIdxUp___closed__0 = _init_l_Lean_Meta_Grind_propagateCtorIdxUp___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_propagateCtorIdxUp___closed__0);
l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2 = _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__2);
l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1 = _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1);
l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0 = _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0);
l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3 = _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
