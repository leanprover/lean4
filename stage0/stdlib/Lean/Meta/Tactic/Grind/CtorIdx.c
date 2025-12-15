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
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4;
lean_object* lean_st_ref_get(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__5;
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
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtorIdxUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
x_3 = lean_unsigned_to_nat(41u);
x_4 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__1;
x_5 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_20);
lean_dec_ref(x_3);
x_21 = lean_array_set(x_4, x_5, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_5, x_22);
lean_dec(x_5);
x_3 = x_19;
x_4 = x_21;
x_5 = x_23;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_5);
x_25 = l_Lean_Expr_constName_x3f(x_3);
lean_dec_ref(x_3);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = l_isCtorIdx_x3f___redArg(x_26, x_13);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 2);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_array_get_size(x_4);
x_37 = lean_nat_add(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_37, x_38);
x_40 = lean_nat_dec_eq(x_36, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
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
x_41 = lean_box(0);
lean_ctor_set(x_28, 0, x_41);
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_188; 
lean_free_object(x_28);
x_42 = l_Array_back_x21___redArg(x_1, x_4);
lean_dec_ref(x_4);
lean_inc(x_42);
x_188 = l_Lean_Meta_Grind_getRootENode___redArg(x_42, x_6, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; uint8_t x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
lean_dec_ref(x_188);
x_190 = lean_ctor_get(x_189, 0);
lean_inc_ref(x_190);
x_191 = lean_ctor_get_uint8(x_189, sizeof(void*)*11 + 2);
x_192 = lean_ctor_get_uint8(x_189, sizeof(void*)*11 + 4);
lean_dec(x_189);
if (x_191 == 0)
{
lean_object* x_251; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_190);
x_251 = lean_infer_type(x_190, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_251) == 0)
{
uint8_t x_252; 
x_252 = !lean_is_exclusive(x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_253 = lean_ctor_get(x_251, 0);
x_254 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__5;
x_255 = l_Lean_Expr_isConstOf(x_253, x_254);
lean_dec(x_253);
if (x_255 == 0)
{
lean_object* x_256; 
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_256 = lean_box(0);
lean_ctor_set(x_251, 0, x_256);
return x_251;
}
else
{
lean_object* x_257; 
lean_free_object(x_251);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_190);
x_257 = l_Lean_Meta_isOffset_x3f(x_190, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
lean_dec_ref(x_257);
if (lean_obj_tag(x_258) == 0)
{
goto block_264;
}
else
{
lean_dec_ref(x_258);
if (x_255 == 0)
{
goto block_264;
}
else
{
x_193 = x_6;
x_194 = x_7;
x_195 = x_8;
x_196 = x_9;
x_197 = x_10;
x_198 = x_11;
x_199 = x_12;
x_200 = x_13;
x_201 = lean_box(0);
goto block_250;
}
}
block_264:
{
lean_object* x_259; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_259 = l_Lean_Meta_getNatValue_x3f(x_190, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
lean_dec_ref(x_259);
if (lean_obj_tag(x_260) == 0)
{
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_15 = lean_box(0);
goto block_18;
}
else
{
lean_dec_ref(x_260);
if (x_255 == 0)
{
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_15 = lean_box(0);
goto block_18;
}
else
{
x_193 = x_6;
x_194 = x_7;
x_195 = x_8;
x_196 = x_9;
x_197 = x_10;
x_198 = x_11;
x_199 = x_12;
x_200 = x_13;
x_201 = lean_box(0);
goto block_250;
}
}
}
else
{
uint8_t x_261; 
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_261 = !lean_is_exclusive(x_259);
if (x_261 == 0)
{
return x_259;
}
else
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_259, 0);
lean_inc(x_262);
lean_dec(x_259);
x_263 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_263, 0, x_262);
return x_263;
}
}
}
}
else
{
uint8_t x_265; 
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_265 = !lean_is_exclusive(x_257);
if (x_265 == 0)
{
return x_257;
}
else
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_257, 0);
lean_inc(x_266);
lean_dec(x_257);
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_266);
return x_267;
}
}
}
}
else
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_268 = lean_ctor_get(x_251, 0);
lean_inc(x_268);
lean_dec(x_251);
x_269 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__5;
x_270 = l_Lean_Expr_isConstOf(x_268, x_269);
lean_dec(x_268);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; 
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_271 = lean_box(0);
x_272 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_272, 0, x_271);
return x_272;
}
else
{
lean_object* x_273; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_190);
x_273 = l_Lean_Meta_isOffset_x3f(x_190, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
lean_dec_ref(x_273);
if (lean_obj_tag(x_274) == 0)
{
goto block_280;
}
else
{
lean_dec_ref(x_274);
if (x_270 == 0)
{
goto block_280;
}
else
{
x_193 = x_6;
x_194 = x_7;
x_195 = x_8;
x_196 = x_9;
x_197 = x_10;
x_198 = x_11;
x_199 = x_12;
x_200 = x_13;
x_201 = lean_box(0);
goto block_250;
}
}
block_280:
{
lean_object* x_275; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_275 = l_Lean_Meta_getNatValue_x3f(x_190, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
lean_dec_ref(x_275);
if (lean_obj_tag(x_276) == 0)
{
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_15 = lean_box(0);
goto block_18;
}
else
{
lean_dec_ref(x_276);
if (x_270 == 0)
{
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_15 = lean_box(0);
goto block_18;
}
else
{
x_193 = x_6;
x_194 = x_7;
x_195 = x_8;
x_196 = x_9;
x_197 = x_10;
x_198 = x_11;
x_199 = x_12;
x_200 = x_13;
x_201 = lean_box(0);
goto block_250;
}
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_277 = lean_ctor_get(x_275, 0);
lean_inc(x_277);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 x_278 = x_275;
} else {
 lean_dec_ref(x_275);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 1, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_277);
return x_279;
}
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_281 = lean_ctor_get(x_273, 0);
lean_inc(x_281);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 x_282 = x_273;
} else {
 lean_dec_ref(x_273);
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
}
else
{
uint8_t x_284; 
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_284 = !lean_is_exclusive(x_251);
if (x_284 == 0)
{
return x_251;
}
else
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_251, 0);
lean_inc(x_285);
lean_dec(x_251);
x_286 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_286, 0, x_285);
return x_286;
}
}
}
else
{
x_193 = x_6;
x_194 = x_7;
x_195 = x_8;
x_196 = x_9;
x_197 = x_10;
x_198 = x_11;
x_199 = x_12;
x_200 = x_13;
x_201 = lean_box(0);
goto block_250;
}
block_250:
{
lean_object* x_202; 
lean_inc(x_200);
lean_inc_ref(x_199);
lean_inc(x_198);
lean_inc_ref(x_197);
lean_inc_ref(x_190);
x_202 = l_Lean_Meta_isConstructorApp_x27_x3f(x_190, x_197, x_198, x_199, x_200);
if (lean_obj_tag(x_202) == 0)
{
uint8_t x_203; 
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_202, 0);
if (lean_obj_tag(x_204) == 1)
{
lean_free_object(x_202);
if (x_192 == 0)
{
lean_object* x_205; 
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec_ref(x_204);
x_43 = x_205;
x_44 = x_190;
x_45 = x_193;
x_46 = x_194;
x_47 = x_195;
x_48 = x_196;
x_49 = x_197;
x_50 = x_198;
x_51 = x_199;
x_52 = x_200;
x_53 = lean_box(0);
goto block_83;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
lean_dec_ref(x_204);
lean_inc(x_200);
lean_inc_ref(x_199);
lean_inc(x_198);
lean_inc_ref(x_197);
lean_inc_ref(x_190);
lean_inc(x_42);
x_207 = l_Lean_Meta_Grind_hasSameType(x_42, x_190, x_197, x_198, x_199, x_200);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = lean_unbox(x_208);
lean_dec(x_208);
if (x_209 == 0)
{
lean_object* x_210; 
lean_dec(x_206);
lean_dec_ref(x_2);
x_210 = l_Lean_Meta_Grind_getGeneration___redArg(x_42, x_193);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec_ref(x_210);
x_212 = l_Lean_Meta_Grind_getGeneration___redArg(x_190, x_193);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; uint8_t x_214; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
lean_dec_ref(x_212);
x_214 = lean_nat_dec_le(x_211, x_213);
if (x_214 == 0)
{
lean_dec(x_213);
x_127 = lean_box(0);
x_128 = x_196;
x_129 = x_197;
x_130 = x_200;
x_131 = x_190;
x_132 = x_193;
x_133 = x_199;
x_134 = x_195;
x_135 = x_198;
x_136 = x_194;
x_137 = x_211;
goto block_187;
}
else
{
lean_dec(x_211);
x_127 = lean_box(0);
x_128 = x_196;
x_129 = x_197;
x_130 = x_200;
x_131 = x_190;
x_132 = x_193;
x_133 = x_199;
x_134 = x_195;
x_135 = x_198;
x_136 = x_194;
x_137 = x_213;
goto block_187;
}
}
else
{
uint8_t x_215; 
lean_dec(x_211);
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
x_215 = !lean_is_exclusive(x_212);
if (x_215 == 0)
{
return x_212;
}
else
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_212, 0);
lean_inc(x_216);
lean_dec(x_212);
x_217 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_217, 0, x_216);
return x_217;
}
}
}
else
{
uint8_t x_218; 
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
x_218 = !lean_is_exclusive(x_210);
if (x_218 == 0)
{
return x_210;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_210, 0);
lean_inc(x_219);
lean_dec(x_210);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_219);
return x_220;
}
}
}
else
{
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
x_43 = x_206;
x_44 = x_190;
x_45 = x_193;
x_46 = x_194;
x_47 = x_195;
x_48 = x_196;
x_49 = x_197;
x_50 = x_198;
x_51 = x_199;
x_52 = x_200;
x_53 = lean_box(0);
goto block_83;
}
}
else
{
uint8_t x_221; 
lean_dec(x_206);
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec_ref(x_2);
x_221 = !lean_is_exclusive(x_207);
if (x_221 == 0)
{
return x_207;
}
else
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_207, 0);
lean_inc(x_222);
lean_dec(x_207);
x_223 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_223, 0, x_222);
return x_223;
}
}
}
}
else
{
lean_object* x_224; 
lean_dec(x_204);
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec_ref(x_2);
x_224 = lean_box(0);
lean_ctor_set(x_202, 0, x_224);
return x_202;
}
}
else
{
lean_object* x_225; 
x_225 = lean_ctor_get(x_202, 0);
lean_inc(x_225);
lean_dec(x_202);
if (lean_obj_tag(x_225) == 1)
{
if (x_192 == 0)
{
lean_object* x_226; 
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_dec_ref(x_225);
x_43 = x_226;
x_44 = x_190;
x_45 = x_193;
x_46 = x_194;
x_47 = x_195;
x_48 = x_196;
x_49 = x_197;
x_50 = x_198;
x_51 = x_199;
x_52 = x_200;
x_53 = lean_box(0);
goto block_83;
}
else
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_225, 0);
lean_inc(x_227);
lean_dec_ref(x_225);
lean_inc(x_200);
lean_inc_ref(x_199);
lean_inc(x_198);
lean_inc_ref(x_197);
lean_inc_ref(x_190);
lean_inc(x_42);
x_228 = l_Lean_Meta_Grind_hasSameType(x_42, x_190, x_197, x_198, x_199, x_200);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; uint8_t x_230; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
lean_dec_ref(x_228);
x_230 = lean_unbox(x_229);
lean_dec(x_229);
if (x_230 == 0)
{
lean_object* x_231; 
lean_dec(x_227);
lean_dec_ref(x_2);
x_231 = l_Lean_Meta_Grind_getGeneration___redArg(x_42, x_193);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
lean_dec_ref(x_231);
x_233 = l_Lean_Meta_Grind_getGeneration___redArg(x_190, x_193);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; uint8_t x_235; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
lean_dec_ref(x_233);
x_235 = lean_nat_dec_le(x_232, x_234);
if (x_235 == 0)
{
lean_dec(x_234);
x_127 = lean_box(0);
x_128 = x_196;
x_129 = x_197;
x_130 = x_200;
x_131 = x_190;
x_132 = x_193;
x_133 = x_199;
x_134 = x_195;
x_135 = x_198;
x_136 = x_194;
x_137 = x_232;
goto block_187;
}
else
{
lean_dec(x_232);
x_127 = lean_box(0);
x_128 = x_196;
x_129 = x_197;
x_130 = x_200;
x_131 = x_190;
x_132 = x_193;
x_133 = x_199;
x_134 = x_195;
x_135 = x_198;
x_136 = x_194;
x_137 = x_234;
goto block_187;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_232);
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
x_236 = lean_ctor_get(x_233, 0);
lean_inc(x_236);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 x_237 = x_233;
} else {
 lean_dec_ref(x_233);
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
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
x_239 = lean_ctor_get(x_231, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_240 = x_231;
} else {
 lean_dec_ref(x_231);
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
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
x_43 = x_227;
x_44 = x_190;
x_45 = x_193;
x_46 = x_194;
x_47 = x_195;
x_48 = x_196;
x_49 = x_197;
x_50 = x_198;
x_51 = x_199;
x_52 = x_200;
x_53 = lean_box(0);
goto block_83;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_227);
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec_ref(x_2);
x_242 = lean_ctor_get(x_228, 0);
lean_inc(x_242);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 x_243 = x_228;
} else {
 lean_dec_ref(x_228);
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
}
else
{
lean_object* x_245; lean_object* x_246; 
lean_dec(x_225);
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec_ref(x_2);
x_245 = lean_box(0);
x_246 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_246, 0, x_245);
return x_246;
}
}
}
else
{
uint8_t x_247; 
lean_dec(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_197);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec_ref(x_190);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec_ref(x_2);
x_247 = !lean_is_exclusive(x_202);
if (x_247 == 0)
{
return x_202;
}
else
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_202, 0);
lean_inc(x_248);
lean_dec(x_202);
x_249 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_249, 0, x_248);
return x_249;
}
}
}
}
else
{
uint8_t x_287; 
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_287 = !lean_is_exclusive(x_188);
if (x_287 == 0)
{
return x_188;
}
else
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_ctor_get(x_188, 0);
lean_inc(x_288);
lean_dec(x_188);
x_289 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_289, 0, x_288);
return x_289;
}
}
block_83:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_43, 2);
lean_inc(x_54);
lean_dec_ref(x_43);
x_55 = l_Lean_mkNatLit(x_54);
x_56 = l_Lean_Meta_Grind_shareCommon___redArg(x_55, x_48);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_box(0);
lean_inc(x_52);
lean_inc_ref(x_51);
lean_inc(x_50);
lean_inc_ref(x_49);
lean_inc(x_48);
lean_inc_ref(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_57);
x_60 = lean_grind_internalize(x_57, x_58, x_59, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
lean_dec_ref(x_60);
lean_inc(x_52);
lean_inc_ref(x_51);
lean_inc(x_50);
lean_inc_ref(x_49);
lean_inc_ref(x_47);
lean_inc(x_45);
x_61 = lean_grind_mk_eq_proof(x_42, x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = l_Lean_Expr_appFn_x21(x_2);
lean_inc(x_52);
lean_inc_ref(x_51);
lean_inc(x_50);
lean_inc_ref(x_49);
x_64 = l_Lean_Meta_mkCongrArg(x_63, x_62, x_49, x_50, x_51, x_52);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
lean_inc(x_52);
lean_inc_ref(x_51);
lean_inc(x_50);
lean_inc_ref(x_49);
lean_inc(x_57);
lean_inc_ref(x_2);
x_66 = l_Lean_Meta_mkEq(x_2, x_57, x_49, x_50, x_51, x_52);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = l_Lean_Meta_mkExpectedPropHint(x_65, x_67);
x_69 = 0;
x_70 = l_Lean_Meta_Grind_pushEqCore___redArg(x_2, x_57, x_68, x_69, x_45, x_47, x_49, x_50, x_51, x_52);
lean_dec_ref(x_47);
lean_dec(x_45);
return x_70;
}
else
{
uint8_t x_71; 
lean_dec(x_65);
lean_dec(x_57);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_47);
lean_dec(x_45);
lean_dec_ref(x_2);
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
return x_66;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_66, 0);
lean_inc(x_72);
lean_dec(x_66);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_57);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_47);
lean_dec(x_45);
lean_dec_ref(x_2);
x_74 = !lean_is_exclusive(x_64);
if (x_74 == 0)
{
return x_64;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_64, 0);
lean_inc(x_75);
lean_dec(x_64);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_57);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_47);
lean_dec(x_45);
lean_dec_ref(x_2);
x_77 = !lean_is_exclusive(x_61);
if (x_77 == 0)
{
return x_61;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_61, 0);
lean_inc(x_78);
lean_dec(x_61);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
else
{
lean_dec(x_57);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_42);
lean_dec_ref(x_2);
return x_60;
}
}
else
{
uint8_t x_80; 
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_42);
lean_dec_ref(x_2);
x_80 = !lean_is_exclusive(x_56);
if (x_80 == 0)
{
return x_56;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_56, 0);
lean_inc(x_81);
lean_dec(x_56);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
block_126:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_inc(x_85);
x_99 = l_Lean_mkConst(x_85, x_87);
x_100 = l_Lean_Meta_Grind_propagateCtorIdxUp___closed__0;
x_101 = l_Lean_Expr_getAppNumArgs(x_84);
lean_inc(x_101);
x_102 = lean_mk_array(x_101, x_100);
x_103 = lean_nat_sub(x_101, x_38);
lean_dec(x_101);
x_104 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_84, x_102, x_103);
x_105 = l_Lean_mkAppN(x_99, x_104);
lean_dec_ref(x_104);
x_106 = l_Lean_Expr_app___override(x_105, x_42);
x_107 = l_Lean_Expr_getAppNumArgs(x_89);
lean_inc(x_107);
x_108 = lean_mk_array(x_107, x_100);
x_109 = lean_nat_sub(x_107, x_38);
lean_dec(x_107);
x_110 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_89, x_108, x_109);
x_111 = l_Lean_mkAppN(x_106, x_110);
lean_dec_ref(x_110);
x_112 = l_Lean_Expr_app___override(x_111, x_86);
lean_inc(x_97);
lean_inc_ref(x_96);
lean_inc(x_95);
lean_inc_ref(x_94);
lean_inc_ref(x_112);
x_113 = lean_infer_type(x_112, x_94, x_95, x_96, x_97);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
if (lean_is_scalar(x_32)) {
 x_115 = lean_alloc_ctor(0, 1, 0);
} else {
 x_115 = x_32;
 lean_ctor_set_tag(x_115, 0);
}
lean_ctor_set(x_115, 0, x_85);
if (lean_is_scalar(x_27)) {
 x_116 = lean_alloc_ctor(7, 1, 0);
} else {
 x_116 = x_27;
 lean_ctor_set_tag(x_116, 7);
}
lean_ctor_set(x_116, 0, x_115);
x_117 = l_Lean_Meta_Grind_addNewRawFact(x_112, x_114, x_88, x_116, x_90, x_91, x_92, x_93, x_94, x_95, x_96, x_97);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec(x_90);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_117, 0);
lean_dec(x_119);
x_120 = lean_box(0);
lean_ctor_set(x_117, 0, x_120);
return x_117;
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_117);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
else
{
return x_117;
}
}
else
{
uint8_t x_123; 
lean_dec_ref(x_112);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
lean_dec(x_85);
lean_dec(x_32);
lean_dec(x_27);
x_123 = !lean_is_exclusive(x_113);
if (x_123 == 0)
{
return x_113;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_113, 0);
lean_inc(x_124);
lean_dec(x_113);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
}
block_187:
{
lean_object* x_138; 
lean_inc(x_130);
lean_inc_ref(x_133);
lean_inc(x_135);
lean_inc_ref(x_129);
lean_inc(x_42);
x_138 = lean_infer_type(x_42, x_129, x_135, x_133, x_130);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec_ref(x_138);
lean_inc(x_130);
lean_inc_ref(x_133);
lean_inc(x_135);
lean_inc_ref(x_129);
x_140 = l_Lean_Meta_whnfD(x_139, x_129, x_135, x_133, x_130);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
lean_inc(x_130);
lean_inc_ref(x_133);
lean_inc(x_135);
lean_inc_ref(x_129);
lean_inc_ref(x_131);
x_142 = lean_infer_type(x_131, x_129, x_135, x_133, x_130);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
lean_inc(x_130);
lean_inc_ref(x_133);
lean_inc(x_135);
lean_inc_ref(x_129);
x_144 = l_Lean_Meta_whnfD(x_143, x_129, x_135, x_133, x_130);
if (lean_obj_tag(x_144) == 0)
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_146 = lean_ctor_get(x_144, 0);
x_147 = lean_ctor_get(x_33, 0);
lean_inc(x_147);
lean_dec_ref(x_33);
lean_inc(x_37);
x_148 = l_Lean_Expr_isAppOfArity(x_141, x_147, x_37);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_147);
lean_free_object(x_144);
lean_dec(x_146);
lean_dec(x_141);
lean_dec(x_137);
lean_dec_ref(x_131);
lean_dec(x_42);
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_27);
x_149 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3;
x_150 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_149, x_132, x_136, x_134, x_128, x_129, x_135, x_133, x_130);
return x_150;
}
else
{
uint8_t x_151; 
x_151 = l_Lean_Expr_isAppOfArity(x_146, x_147, x_37);
if (x_151 == 0)
{
lean_object* x_152; 
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_141);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec(x_42);
lean_dec(x_32);
lean_dec(x_27);
x_152 = lean_box(0);
lean_ctor_set(x_144, 0, x_152);
return x_144;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
lean_free_object(x_144);
x_153 = lean_st_ref_get(x_130);
x_154 = lean_ctor_get(x_153, 0);
lean_inc_ref(x_154);
lean_dec(x_153);
x_155 = l_Lean_Expr_getAppFn(x_141);
x_156 = l_Lean_Expr_constLevels_x21(x_155);
lean_dec_ref(x_155);
x_157 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_147);
x_158 = l_Lean_Environment_containsOnBranch(x_154, x_157);
if (x_158 == 0)
{
lean_object* x_159; 
lean_inc(x_130);
lean_inc_ref(x_133);
lean_inc(x_157);
x_159 = l_Lean_executeReservedNameAction(x_157, x_133, x_130);
if (lean_obj_tag(x_159) == 0)
{
lean_dec_ref(x_159);
x_84 = x_141;
x_85 = x_157;
x_86 = x_131;
x_87 = x_156;
x_88 = x_137;
x_89 = x_146;
x_90 = x_132;
x_91 = x_136;
x_92 = x_134;
x_93 = x_128;
x_94 = x_129;
x_95 = x_135;
x_96 = x_133;
x_97 = x_130;
x_98 = lean_box(0);
goto block_126;
}
else
{
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_146);
lean_dec(x_141);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec(x_42);
lean_dec(x_32);
lean_dec(x_27);
return x_159;
}
}
else
{
x_84 = x_141;
x_85 = x_157;
x_86 = x_131;
x_87 = x_156;
x_88 = x_137;
x_89 = x_146;
x_90 = x_132;
x_91 = x_136;
x_92 = x_134;
x_93 = x_128;
x_94 = x_129;
x_95 = x_135;
x_96 = x_133;
x_97 = x_130;
x_98 = lean_box(0);
goto block_126;
}
}
}
}
else
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_144, 0);
lean_inc(x_160);
lean_dec(x_144);
x_161 = lean_ctor_get(x_33, 0);
lean_inc(x_161);
lean_dec_ref(x_33);
lean_inc(x_37);
x_162 = l_Lean_Expr_isAppOfArity(x_141, x_161, x_37);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_141);
lean_dec(x_137);
lean_dec_ref(x_131);
lean_dec(x_42);
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_27);
x_163 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3;
x_164 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_163, x_132, x_136, x_134, x_128, x_129, x_135, x_133, x_130);
return x_164;
}
else
{
uint8_t x_165; 
x_165 = l_Lean_Expr_isAppOfArity(x_160, x_161, x_37);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_141);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec(x_42);
lean_dec(x_32);
lean_dec(x_27);
x_166 = lean_box(0);
x_167 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_168 = lean_st_ref_get(x_130);
x_169 = lean_ctor_get(x_168, 0);
lean_inc_ref(x_169);
lean_dec(x_168);
x_170 = l_Lean_Expr_getAppFn(x_141);
x_171 = l_Lean_Expr_constLevels_x21(x_170);
lean_dec_ref(x_170);
x_172 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_161);
x_173 = l_Lean_Environment_containsOnBranch(x_169, x_172);
if (x_173 == 0)
{
lean_object* x_174; 
lean_inc(x_130);
lean_inc_ref(x_133);
lean_inc(x_172);
x_174 = l_Lean_executeReservedNameAction(x_172, x_133, x_130);
if (lean_obj_tag(x_174) == 0)
{
lean_dec_ref(x_174);
x_84 = x_141;
x_85 = x_172;
x_86 = x_131;
x_87 = x_171;
x_88 = x_137;
x_89 = x_160;
x_90 = x_132;
x_91 = x_136;
x_92 = x_134;
x_93 = x_128;
x_94 = x_129;
x_95 = x_135;
x_96 = x_133;
x_97 = x_130;
x_98 = lean_box(0);
goto block_126;
}
else
{
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_160);
lean_dec(x_141);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec(x_42);
lean_dec(x_32);
lean_dec(x_27);
return x_174;
}
}
else
{
x_84 = x_141;
x_85 = x_172;
x_86 = x_131;
x_87 = x_171;
x_88 = x_137;
x_89 = x_160;
x_90 = x_132;
x_91 = x_136;
x_92 = x_134;
x_93 = x_128;
x_94 = x_129;
x_95 = x_135;
x_96 = x_133;
x_97 = x_130;
x_98 = lean_box(0);
goto block_126;
}
}
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_141);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
x_175 = !lean_is_exclusive(x_144);
if (x_175 == 0)
{
return x_144;
}
else
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_144, 0);
lean_inc(x_176);
lean_dec(x_144);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_176);
return x_177;
}
}
}
else
{
uint8_t x_178; 
lean_dec(x_141);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
x_178 = !lean_is_exclusive(x_142);
if (x_178 == 0)
{
return x_142;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_142, 0);
lean_inc(x_179);
lean_dec(x_142);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_179);
return x_180;
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
x_181 = !lean_is_exclusive(x_140);
if (x_181 == 0)
{
return x_140;
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_140, 0);
lean_inc(x_182);
lean_dec(x_140);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_182);
return x_183;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec_ref(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec(x_42);
lean_dec(x_37);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_27);
x_184 = !lean_is_exclusive(x_138);
if (x_184 == 0)
{
return x_138;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_138, 0);
lean_inc(x_185);
lean_dec(x_138);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_185);
return x_186;
}
}
}
}
}
else
{
lean_object* x_290; 
lean_dec(x_30);
lean_dec(x_27);
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
x_290 = lean_box(0);
lean_ctor_set(x_28, 0, x_290);
return x_28;
}
}
else
{
lean_object* x_291; 
x_291 = lean_ctor_get(x_28, 0);
lean_inc(x_291);
lean_dec(x_28);
if (lean_obj_tag(x_291) == 1)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_293 = x_291;
} else {
 lean_dec_ref(x_291);
 x_293 = lean_box(0);
}
x_294 = lean_ctor_get(x_292, 0);
lean_inc_ref(x_294);
x_295 = lean_ctor_get(x_292, 1);
lean_inc(x_295);
x_296 = lean_ctor_get(x_292, 2);
lean_inc(x_296);
lean_dec(x_292);
x_297 = lean_array_get_size(x_4);
x_298 = lean_nat_add(x_295, x_296);
lean_dec(x_296);
lean_dec(x_295);
x_299 = lean_unsigned_to_nat(1u);
x_300 = lean_nat_add(x_298, x_299);
x_301 = lean_nat_dec_eq(x_297, x_300);
lean_dec(x_300);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; 
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
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
x_302 = lean_box(0);
x_303 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_303, 0, x_302);
return x_303;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_434; 
x_304 = l_Array_back_x21___redArg(x_1, x_4);
lean_dec_ref(x_4);
lean_inc(x_304);
x_434 = l_Lean_Meta_Grind_getRootENode___redArg(x_304, x_6, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; uint8_t x_437; uint8_t x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
lean_dec_ref(x_434);
x_436 = lean_ctor_get(x_435, 0);
lean_inc_ref(x_436);
x_437 = lean_ctor_get_uint8(x_435, sizeof(void*)*11 + 2);
x_438 = lean_ctor_get_uint8(x_435, sizeof(void*)*11 + 4);
lean_dec(x_435);
if (x_437 == 0)
{
lean_object* x_476; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_436);
x_476 = lean_infer_type(x_436, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 x_478 = x_476;
} else {
 lean_dec_ref(x_476);
 x_478 = lean_box(0);
}
x_479 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__5;
x_480 = l_Lean_Expr_isConstOf(x_477, x_479);
lean_dec(x_477);
if (x_480 == 0)
{
lean_object* x_481; lean_object* x_482; 
lean_dec_ref(x_436);
lean_dec(x_304);
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_481 = lean_box(0);
if (lean_is_scalar(x_478)) {
 x_482 = lean_alloc_ctor(0, 1, 0);
} else {
 x_482 = x_478;
}
lean_ctor_set(x_482, 0, x_481);
return x_482;
}
else
{
lean_object* x_483; 
lean_dec(x_478);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_436);
x_483 = l_Lean_Meta_isOffset_x3f(x_436, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; 
x_484 = lean_ctor_get(x_483, 0);
lean_inc(x_484);
lean_dec_ref(x_483);
if (lean_obj_tag(x_484) == 0)
{
goto block_490;
}
else
{
lean_dec_ref(x_484);
if (x_480 == 0)
{
goto block_490;
}
else
{
x_439 = x_6;
x_440 = x_7;
x_441 = x_8;
x_442 = x_9;
x_443 = x_10;
x_444 = x_11;
x_445 = x_12;
x_446 = x_13;
x_447 = lean_box(0);
goto block_475;
}
}
block_490:
{
lean_object* x_485; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_485 = l_Lean_Meta_getNatValue_x3f(x_436, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
lean_dec_ref(x_485);
if (lean_obj_tag(x_486) == 0)
{
lean_dec_ref(x_436);
lean_dec(x_304);
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_15 = lean_box(0);
goto block_18;
}
else
{
lean_dec_ref(x_486);
if (x_480 == 0)
{
lean_dec_ref(x_436);
lean_dec(x_304);
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_15 = lean_box(0);
goto block_18;
}
else
{
x_439 = x_6;
x_440 = x_7;
x_441 = x_8;
x_442 = x_9;
x_443 = x_10;
x_444 = x_11;
x_445 = x_12;
x_446 = x_13;
x_447 = lean_box(0);
goto block_475;
}
}
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
lean_dec_ref(x_436);
lean_dec(x_304);
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_487 = lean_ctor_get(x_485, 0);
lean_inc(x_487);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 x_488 = x_485;
} else {
 lean_dec_ref(x_485);
 x_488 = lean_box(0);
}
if (lean_is_scalar(x_488)) {
 x_489 = lean_alloc_ctor(1, 1, 0);
} else {
 x_489 = x_488;
}
lean_ctor_set(x_489, 0, x_487);
return x_489;
}
}
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
lean_dec_ref(x_436);
lean_dec(x_304);
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_491 = lean_ctor_get(x_483, 0);
lean_inc(x_491);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 x_492 = x_483;
} else {
 lean_dec_ref(x_483);
 x_492 = lean_box(0);
}
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(1, 1, 0);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_491);
return x_493;
}
}
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec_ref(x_436);
lean_dec(x_304);
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_494 = lean_ctor_get(x_476, 0);
lean_inc(x_494);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 x_495 = x_476;
} else {
 lean_dec_ref(x_476);
 x_495 = lean_box(0);
}
if (lean_is_scalar(x_495)) {
 x_496 = lean_alloc_ctor(1, 1, 0);
} else {
 x_496 = x_495;
}
lean_ctor_set(x_496, 0, x_494);
return x_496;
}
}
else
{
x_439 = x_6;
x_440 = x_7;
x_441 = x_8;
x_442 = x_9;
x_443 = x_10;
x_444 = x_11;
x_445 = x_12;
x_446 = x_13;
x_447 = lean_box(0);
goto block_475;
}
block_475:
{
lean_object* x_448; 
lean_inc(x_446);
lean_inc_ref(x_445);
lean_inc(x_444);
lean_inc_ref(x_443);
lean_inc_ref(x_436);
x_448 = l_Lean_Meta_isConstructorApp_x27_x3f(x_436, x_443, x_444, x_445, x_446);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 x_450 = x_448;
} else {
 lean_dec_ref(x_448);
 x_450 = lean_box(0);
}
if (lean_obj_tag(x_449) == 1)
{
lean_dec(x_450);
if (x_438 == 0)
{
lean_object* x_451; 
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
x_451 = lean_ctor_get(x_449, 0);
lean_inc(x_451);
lean_dec_ref(x_449);
x_305 = x_451;
x_306 = x_436;
x_307 = x_439;
x_308 = x_440;
x_309 = x_441;
x_310 = x_442;
x_311 = x_443;
x_312 = x_444;
x_313 = x_445;
x_314 = x_446;
x_315 = lean_box(0);
goto block_345;
}
else
{
lean_object* x_452; lean_object* x_453; 
x_452 = lean_ctor_get(x_449, 0);
lean_inc(x_452);
lean_dec_ref(x_449);
lean_inc(x_446);
lean_inc_ref(x_445);
lean_inc(x_444);
lean_inc_ref(x_443);
lean_inc_ref(x_436);
lean_inc(x_304);
x_453 = l_Lean_Meta_Grind_hasSameType(x_304, x_436, x_443, x_444, x_445, x_446);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; uint8_t x_455; 
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
lean_dec_ref(x_453);
x_455 = lean_unbox(x_454);
lean_dec(x_454);
if (x_455 == 0)
{
lean_object* x_456; 
lean_dec(x_452);
lean_dec_ref(x_2);
x_456 = l_Lean_Meta_Grind_getGeneration___redArg(x_304, x_439);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
lean_dec_ref(x_456);
x_458 = l_Lean_Meta_Grind_getGeneration___redArg(x_436, x_439);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; uint8_t x_460; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
lean_dec_ref(x_458);
x_460 = lean_nat_dec_le(x_457, x_459);
if (x_460 == 0)
{
lean_dec(x_459);
x_387 = lean_box(0);
x_388 = x_442;
x_389 = x_443;
x_390 = x_446;
x_391 = x_436;
x_392 = x_439;
x_393 = x_445;
x_394 = x_441;
x_395 = x_444;
x_396 = x_440;
x_397 = x_457;
goto block_433;
}
else
{
lean_dec(x_457);
x_387 = lean_box(0);
x_388 = x_442;
x_389 = x_443;
x_390 = x_446;
x_391 = x_436;
x_392 = x_439;
x_393 = x_445;
x_394 = x_441;
x_395 = x_444;
x_396 = x_440;
x_397 = x_459;
goto block_433;
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_457);
lean_dec(x_446);
lean_dec_ref(x_445);
lean_dec(x_444);
lean_dec_ref(x_443);
lean_dec(x_442);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec_ref(x_436);
lean_dec(x_304);
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
x_461 = lean_ctor_get(x_458, 0);
lean_inc(x_461);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 x_462 = x_458;
} else {
 lean_dec_ref(x_458);
 x_462 = lean_box(0);
}
if (lean_is_scalar(x_462)) {
 x_463 = lean_alloc_ctor(1, 1, 0);
} else {
 x_463 = x_462;
}
lean_ctor_set(x_463, 0, x_461);
return x_463;
}
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
lean_dec(x_446);
lean_dec_ref(x_445);
lean_dec(x_444);
lean_dec_ref(x_443);
lean_dec(x_442);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec_ref(x_436);
lean_dec(x_304);
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
x_464 = lean_ctor_get(x_456, 0);
lean_inc(x_464);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 x_465 = x_456;
} else {
 lean_dec_ref(x_456);
 x_465 = lean_box(0);
}
if (lean_is_scalar(x_465)) {
 x_466 = lean_alloc_ctor(1, 1, 0);
} else {
 x_466 = x_465;
}
lean_ctor_set(x_466, 0, x_464);
return x_466;
}
}
else
{
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
x_305 = x_452;
x_306 = x_436;
x_307 = x_439;
x_308 = x_440;
x_309 = x_441;
x_310 = x_442;
x_311 = x_443;
x_312 = x_444;
x_313 = x_445;
x_314 = x_446;
x_315 = lean_box(0);
goto block_345;
}
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_dec(x_452);
lean_dec(x_446);
lean_dec_ref(x_445);
lean_dec(x_444);
lean_dec_ref(x_443);
lean_dec(x_442);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec_ref(x_436);
lean_dec(x_304);
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
lean_dec_ref(x_2);
x_467 = lean_ctor_get(x_453, 0);
lean_inc(x_467);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 x_468 = x_453;
} else {
 lean_dec_ref(x_453);
 x_468 = lean_box(0);
}
if (lean_is_scalar(x_468)) {
 x_469 = lean_alloc_ctor(1, 1, 0);
} else {
 x_469 = x_468;
}
lean_ctor_set(x_469, 0, x_467);
return x_469;
}
}
}
else
{
lean_object* x_470; lean_object* x_471; 
lean_dec(x_449);
lean_dec(x_446);
lean_dec_ref(x_445);
lean_dec(x_444);
lean_dec_ref(x_443);
lean_dec(x_442);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec_ref(x_436);
lean_dec(x_304);
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
lean_dec_ref(x_2);
x_470 = lean_box(0);
if (lean_is_scalar(x_450)) {
 x_471 = lean_alloc_ctor(0, 1, 0);
} else {
 x_471 = x_450;
}
lean_ctor_set(x_471, 0, x_470);
return x_471;
}
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_446);
lean_dec_ref(x_445);
lean_dec(x_444);
lean_dec_ref(x_443);
lean_dec(x_442);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec_ref(x_436);
lean_dec(x_304);
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
lean_dec_ref(x_2);
x_472 = lean_ctor_get(x_448, 0);
lean_inc(x_472);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 x_473 = x_448;
} else {
 lean_dec_ref(x_448);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 1, 0);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_472);
return x_474;
}
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; 
lean_dec(x_304);
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_497 = lean_ctor_get(x_434, 0);
lean_inc(x_497);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 x_498 = x_434;
} else {
 lean_dec_ref(x_434);
 x_498 = lean_box(0);
}
if (lean_is_scalar(x_498)) {
 x_499 = lean_alloc_ctor(1, 1, 0);
} else {
 x_499 = x_498;
}
lean_ctor_set(x_499, 0, x_497);
return x_499;
}
block_345:
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_305, 2);
lean_inc(x_316);
lean_dec_ref(x_305);
x_317 = l_Lean_mkNatLit(x_316);
x_318 = l_Lean_Meta_Grind_shareCommon___redArg(x_317, x_310);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
lean_dec_ref(x_318);
x_320 = lean_unsigned_to_nat(0u);
x_321 = lean_box(0);
lean_inc(x_314);
lean_inc_ref(x_313);
lean_inc(x_312);
lean_inc_ref(x_311);
lean_inc(x_310);
lean_inc_ref(x_309);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_319);
x_322 = lean_grind_internalize(x_319, x_320, x_321, x_307, x_308, x_309, x_310, x_311, x_312, x_313, x_314);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; 
lean_dec_ref(x_322);
lean_inc(x_314);
lean_inc_ref(x_313);
lean_inc(x_312);
lean_inc_ref(x_311);
lean_inc_ref(x_309);
lean_inc(x_307);
x_323 = lean_grind_mk_eq_proof(x_304, x_306, x_307, x_308, x_309, x_310, x_311, x_312, x_313, x_314);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
lean_dec_ref(x_323);
x_325 = l_Lean_Expr_appFn_x21(x_2);
lean_inc(x_314);
lean_inc_ref(x_313);
lean_inc(x_312);
lean_inc_ref(x_311);
x_326 = l_Lean_Meta_mkCongrArg(x_325, x_324, x_311, x_312, x_313, x_314);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
lean_dec_ref(x_326);
lean_inc(x_314);
lean_inc_ref(x_313);
lean_inc(x_312);
lean_inc_ref(x_311);
lean_inc(x_319);
lean_inc_ref(x_2);
x_328 = l_Lean_Meta_mkEq(x_2, x_319, x_311, x_312, x_313, x_314);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
lean_dec_ref(x_328);
x_330 = l_Lean_Meta_mkExpectedPropHint(x_327, x_329);
x_331 = 0;
x_332 = l_Lean_Meta_Grind_pushEqCore___redArg(x_2, x_319, x_330, x_331, x_307, x_309, x_311, x_312, x_313, x_314);
lean_dec_ref(x_309);
lean_dec(x_307);
return x_332;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_327);
lean_dec(x_319);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec_ref(x_309);
lean_dec(x_307);
lean_dec_ref(x_2);
x_333 = lean_ctor_get(x_328, 0);
lean_inc(x_333);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 x_334 = x_328;
} else {
 lean_dec_ref(x_328);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 1, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_333);
return x_335;
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_319);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec_ref(x_309);
lean_dec(x_307);
lean_dec_ref(x_2);
x_336 = lean_ctor_get(x_326, 0);
lean_inc(x_336);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 x_337 = x_326;
} else {
 lean_dec_ref(x_326);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 1, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_336);
return x_338;
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_319);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec_ref(x_309);
lean_dec(x_307);
lean_dec_ref(x_2);
x_339 = lean_ctor_get(x_323, 0);
lean_inc(x_339);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 x_340 = x_323;
} else {
 lean_dec_ref(x_323);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 1, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_339);
return x_341;
}
}
else
{
lean_dec(x_319);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec(x_307);
lean_dec_ref(x_306);
lean_dec(x_304);
lean_dec_ref(x_2);
return x_322;
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec(x_307);
lean_dec_ref(x_306);
lean_dec(x_304);
lean_dec_ref(x_2);
x_342 = lean_ctor_get(x_318, 0);
lean_inc(x_342);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 x_343 = x_318;
} else {
 lean_dec_ref(x_318);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(1, 1, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_342);
return x_344;
}
}
block_386:
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_inc(x_347);
x_361 = l_Lean_mkConst(x_347, x_349);
x_362 = l_Lean_Meta_Grind_propagateCtorIdxUp___closed__0;
x_363 = l_Lean_Expr_getAppNumArgs(x_346);
lean_inc(x_363);
x_364 = lean_mk_array(x_363, x_362);
x_365 = lean_nat_sub(x_363, x_299);
lean_dec(x_363);
x_366 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_346, x_364, x_365);
x_367 = l_Lean_mkAppN(x_361, x_366);
lean_dec_ref(x_366);
x_368 = l_Lean_Expr_app___override(x_367, x_304);
x_369 = l_Lean_Expr_getAppNumArgs(x_351);
lean_inc(x_369);
x_370 = lean_mk_array(x_369, x_362);
x_371 = lean_nat_sub(x_369, x_299);
lean_dec(x_369);
x_372 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_351, x_370, x_371);
x_373 = l_Lean_mkAppN(x_368, x_372);
lean_dec_ref(x_372);
x_374 = l_Lean_Expr_app___override(x_373, x_348);
lean_inc(x_359);
lean_inc_ref(x_358);
lean_inc(x_357);
lean_inc_ref(x_356);
lean_inc_ref(x_374);
x_375 = lean_infer_type(x_374, x_356, x_357, x_358, x_359);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
lean_dec_ref(x_375);
if (lean_is_scalar(x_293)) {
 x_377 = lean_alloc_ctor(0, 1, 0);
} else {
 x_377 = x_293;
 lean_ctor_set_tag(x_377, 0);
}
lean_ctor_set(x_377, 0, x_347);
if (lean_is_scalar(x_27)) {
 x_378 = lean_alloc_ctor(7, 1, 0);
} else {
 x_378 = x_27;
 lean_ctor_set_tag(x_378, 7);
}
lean_ctor_set(x_378, 0, x_377);
x_379 = l_Lean_Meta_Grind_addNewRawFact(x_374, x_376, x_350, x_378, x_352, x_353, x_354, x_355, x_356, x_357, x_358, x_359);
lean_dec(x_355);
lean_dec_ref(x_354);
lean_dec(x_353);
lean_dec(x_352);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 x_380 = x_379;
} else {
 lean_dec_ref(x_379);
 x_380 = lean_box(0);
}
x_381 = lean_box(0);
if (lean_is_scalar(x_380)) {
 x_382 = lean_alloc_ctor(0, 1, 0);
} else {
 x_382 = x_380;
}
lean_ctor_set(x_382, 0, x_381);
return x_382;
}
else
{
return x_379;
}
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec_ref(x_374);
lean_dec(x_359);
lean_dec_ref(x_358);
lean_dec(x_357);
lean_dec_ref(x_356);
lean_dec(x_355);
lean_dec_ref(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_350);
lean_dec(x_347);
lean_dec(x_293);
lean_dec(x_27);
x_383 = lean_ctor_get(x_375, 0);
lean_inc(x_383);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 x_384 = x_375;
} else {
 lean_dec_ref(x_375);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(1, 1, 0);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_383);
return x_385;
}
}
block_433:
{
lean_object* x_398; 
lean_inc(x_390);
lean_inc_ref(x_393);
lean_inc(x_395);
lean_inc_ref(x_389);
lean_inc(x_304);
x_398 = lean_infer_type(x_304, x_389, x_395, x_393, x_390);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
lean_dec_ref(x_398);
lean_inc(x_390);
lean_inc_ref(x_393);
lean_inc(x_395);
lean_inc_ref(x_389);
x_400 = l_Lean_Meta_whnfD(x_399, x_389, x_395, x_393, x_390);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
lean_dec_ref(x_400);
lean_inc(x_390);
lean_inc_ref(x_393);
lean_inc(x_395);
lean_inc_ref(x_389);
lean_inc_ref(x_391);
x_402 = lean_infer_type(x_391, x_389, x_395, x_393, x_390);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
lean_dec_ref(x_402);
lean_inc(x_390);
lean_inc_ref(x_393);
lean_inc(x_395);
lean_inc_ref(x_389);
x_404 = l_Lean_Meta_whnfD(x_403, x_389, x_395, x_393, x_390);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 x_406 = x_404;
} else {
 lean_dec_ref(x_404);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_294, 0);
lean_inc(x_407);
lean_dec_ref(x_294);
lean_inc(x_298);
x_408 = l_Lean_Expr_isAppOfArity(x_401, x_407, x_298);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; 
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_401);
lean_dec(x_397);
lean_dec_ref(x_391);
lean_dec(x_304);
lean_dec(x_298);
lean_dec(x_293);
lean_dec(x_27);
x_409 = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__3;
x_410 = l_panic___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__0(x_409, x_392, x_396, x_394, x_388, x_389, x_395, x_393, x_390);
return x_410;
}
else
{
uint8_t x_411; 
x_411 = l_Lean_Expr_isAppOfArity(x_405, x_407, x_298);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; 
lean_dec(x_407);
lean_dec(x_405);
lean_dec(x_401);
lean_dec(x_397);
lean_dec(x_396);
lean_dec(x_395);
lean_dec_ref(x_394);
lean_dec_ref(x_393);
lean_dec(x_392);
lean_dec_ref(x_391);
lean_dec(x_390);
lean_dec_ref(x_389);
lean_dec(x_388);
lean_dec(x_304);
lean_dec(x_293);
lean_dec(x_27);
x_412 = lean_box(0);
if (lean_is_scalar(x_406)) {
 x_413 = lean_alloc_ctor(0, 1, 0);
} else {
 x_413 = x_406;
}
lean_ctor_set(x_413, 0, x_412);
return x_413;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; 
lean_dec(x_406);
x_414 = lean_st_ref_get(x_390);
x_415 = lean_ctor_get(x_414, 0);
lean_inc_ref(x_415);
lean_dec(x_414);
x_416 = l_Lean_Expr_getAppFn(x_401);
x_417 = l_Lean_Expr_constLevels_x21(x_416);
lean_dec_ref(x_416);
x_418 = l_Lean_Meta_mkCtorIdxHInjTheoremNameFor(x_407);
x_419 = l_Lean_Environment_containsOnBranch(x_415, x_418);
if (x_419 == 0)
{
lean_object* x_420; 
lean_inc(x_390);
lean_inc_ref(x_393);
lean_inc(x_418);
x_420 = l_Lean_executeReservedNameAction(x_418, x_393, x_390);
if (lean_obj_tag(x_420) == 0)
{
lean_dec_ref(x_420);
x_346 = x_401;
x_347 = x_418;
x_348 = x_391;
x_349 = x_417;
x_350 = x_397;
x_351 = x_405;
x_352 = x_392;
x_353 = x_396;
x_354 = x_394;
x_355 = x_388;
x_356 = x_389;
x_357 = x_395;
x_358 = x_393;
x_359 = x_390;
x_360 = lean_box(0);
goto block_386;
}
else
{
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_405);
lean_dec(x_401);
lean_dec(x_397);
lean_dec(x_396);
lean_dec(x_395);
lean_dec_ref(x_394);
lean_dec_ref(x_393);
lean_dec(x_392);
lean_dec_ref(x_391);
lean_dec(x_390);
lean_dec_ref(x_389);
lean_dec(x_388);
lean_dec(x_304);
lean_dec(x_293);
lean_dec(x_27);
return x_420;
}
}
else
{
x_346 = x_401;
x_347 = x_418;
x_348 = x_391;
x_349 = x_417;
x_350 = x_397;
x_351 = x_405;
x_352 = x_392;
x_353 = x_396;
x_354 = x_394;
x_355 = x_388;
x_356 = x_389;
x_357 = x_395;
x_358 = x_393;
x_359 = x_390;
x_360 = lean_box(0);
goto block_386;
}
}
}
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_401);
lean_dec(x_397);
lean_dec(x_396);
lean_dec(x_395);
lean_dec_ref(x_394);
lean_dec_ref(x_393);
lean_dec(x_392);
lean_dec_ref(x_391);
lean_dec(x_390);
lean_dec_ref(x_389);
lean_dec(x_388);
lean_dec(x_304);
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
x_421 = lean_ctor_get(x_404, 0);
lean_inc(x_421);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 x_422 = x_404;
} else {
 lean_dec_ref(x_404);
 x_422 = lean_box(0);
}
if (lean_is_scalar(x_422)) {
 x_423 = lean_alloc_ctor(1, 1, 0);
} else {
 x_423 = x_422;
}
lean_ctor_set(x_423, 0, x_421);
return x_423;
}
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_401);
lean_dec(x_397);
lean_dec(x_396);
lean_dec(x_395);
lean_dec_ref(x_394);
lean_dec_ref(x_393);
lean_dec(x_392);
lean_dec_ref(x_391);
lean_dec(x_390);
lean_dec_ref(x_389);
lean_dec(x_388);
lean_dec(x_304);
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
x_424 = lean_ctor_get(x_402, 0);
lean_inc(x_424);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 x_425 = x_402;
} else {
 lean_dec_ref(x_402);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(1, 1, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_424);
return x_426;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_397);
lean_dec(x_396);
lean_dec(x_395);
lean_dec_ref(x_394);
lean_dec_ref(x_393);
lean_dec(x_392);
lean_dec_ref(x_391);
lean_dec(x_390);
lean_dec_ref(x_389);
lean_dec(x_388);
lean_dec(x_304);
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
x_427 = lean_ctor_get(x_400, 0);
lean_inc(x_427);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 x_428 = x_400;
} else {
 lean_dec_ref(x_400);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(1, 1, 0);
} else {
 x_429 = x_428;
}
lean_ctor_set(x_429, 0, x_427);
return x_429;
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_397);
lean_dec(x_396);
lean_dec(x_395);
lean_dec_ref(x_394);
lean_dec_ref(x_393);
lean_dec(x_392);
lean_dec_ref(x_391);
lean_dec(x_390);
lean_dec_ref(x_389);
lean_dec(x_388);
lean_dec(x_304);
lean_dec(x_298);
lean_dec_ref(x_294);
lean_dec(x_293);
lean_dec(x_27);
x_430 = lean_ctor_get(x_398, 0);
lean_inc(x_430);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 x_431 = x_398;
} else {
 lean_dec_ref(x_398);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 1, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_430);
return x_432;
}
}
}
}
else
{
lean_object* x_500; lean_object* x_501; 
lean_dec(x_291);
lean_dec(x_27);
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
x_500 = lean_box(0);
x_501 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_501, 0, x_500);
return x_501;
}
}
}
else
{
uint8_t x_502; 
lean_dec(x_27);
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
x_502 = !lean_is_exclusive(x_28);
if (x_502 == 0)
{
return x_28;
}
else
{
lean_object* x_503; lean_object* x_504; 
x_503 = lean_ctor_get(x_28, 0);
lean_inc(x_503);
lean_dec(x_28);
x_504 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_504, 0, x_503);
return x_504;
}
}
}
else
{
lean_object* x_505; lean_object* x_506; 
lean_dec(x_25);
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
x_505 = lean_box(0);
x_506 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_506, 0, x_505);
return x_506;
}
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
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
l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4 = _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__4);
l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__5 = _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_propagateCtorIdxUp_spec__1___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
