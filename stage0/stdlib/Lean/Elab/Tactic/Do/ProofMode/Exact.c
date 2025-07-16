// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Exact
// Imports: Std.Tactic.Do.Syntax Lean.Elab.Tactic.Do.ProofMode.Basic Lean.Elab.Tactic.Do.ProofMode.Focus Lean.Elab.Tactic.ElabTerm
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__12;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__5;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__9;
lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__0;
lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__4;
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__0;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__1;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__7;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__3;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__9;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6;
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__0;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__2;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__4;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__11;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__1;
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Do", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("SPred", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Exact", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assumption", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__5;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__4;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2;
x_5 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1;
x_6 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0;
x_7 = l_Lean_Name_mkStr6(x_6, x_5, x_4, x_3, x_2, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mexact tactic failed, hypothesis ", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" is not definitionally equal to ", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Syntax_getId(x_2);
lean_inc_ref(x_1);
x_9 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f(x_1, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_14 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_20);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_23);
lean_dec(x_15);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_20);
x_24 = l_Lean_Meta_isExprDefEq(x_21, x_20, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6;
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Expr_const___override(x_28, x_30);
lean_inc_ref(x_20);
x_32 = l_Lean_mkApp5(x_31, x_18, x_19, x_22, x_20, x_23);
x_33 = lean_unbox(x_26);
lean_dec(x_26);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec_ref(x_32);
lean_free_object(x_24);
lean_free_object(x_9);
x_34 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8;
x_35 = l_Lean_MessageData_ofSyntax(x_2);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_MessageData_ofExpr(x_20);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__12;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_42, x_3, x_4, x_5, x_6, x_27);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_dec_ref(x_20);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_ctor_set(x_9, 0, x_32);
lean_ctor_set(x_24, 0, x_9);
return x_24;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_24, 0);
x_49 = lean_ctor_get(x_24, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_24);
x_50 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6;
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_17);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Expr_const___override(x_50, x_52);
lean_inc_ref(x_20);
x_54 = l_Lean_mkApp5(x_53, x_18, x_19, x_22, x_20, x_23);
x_55 = lean_unbox(x_48);
lean_dec(x_48);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_54);
lean_free_object(x_9);
x_56 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8;
x_57 = l_Lean_MessageData_ofSyntax(x_2);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_MessageData_ofExpr(x_20);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__12;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_64, x_3, x_4, x_5, x_6, x_49);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
else
{
lean_object* x_70; 
lean_dec_ref(x_20);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_ctor_set(x_9, 0, x_54);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_9);
lean_ctor_set(x_70, 1, x_49);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_free_object(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_24);
if (x_71 == 0)
{
return x_24;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_24, 0);
x_73 = lean_ctor_get(x_24, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_24);
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
lean_free_object(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_75 = !lean_is_exclusive(x_14);
if (x_75 == 0)
{
return x_14;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_14, 0);
x_77 = lean_ctor_get(x_14, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_14);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; 
lean_dec(x_9);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_79 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = lean_ctor_get(x_1, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_85);
lean_dec_ref(x_1);
x_86 = lean_ctor_get(x_80, 0);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_80, 1);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_80, 2);
lean_inc_ref(x_88);
lean_dec(x_80);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_85);
x_89 = l_Lean_Meta_isExprDefEq(x_86, x_85, x_3, x_4, x_5, x_6, x_81);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
x_93 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6;
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_82);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Expr_const___override(x_93, x_95);
lean_inc_ref(x_85);
x_97 = l_Lean_mkApp5(x_96, x_83, x_84, x_87, x_85, x_88);
x_98 = lean_unbox(x_90);
lean_dec(x_90);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec_ref(x_97);
lean_dec(x_92);
x_99 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8;
x_100 = l_Lean_MessageData_ofSyntax(x_2);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10;
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_MessageData_ofExpr(x_85);
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__12;
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_107, x_3, x_4, x_5, x_6, x_91);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec_ref(x_85);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_97);
if (lean_is_scalar(x_92)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_92;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_91);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec_ref(x_88);
lean_dec_ref(x_87);
lean_dec_ref(x_85);
lean_dec_ref(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_115 = lean_ctor_get(x_89, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_89, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_117 = x_89;
} else {
 lean_dec_ref(x_89);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_119 = lean_ctor_get(x_79, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_79, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_121 = x_79;
} else {
 lean_dec_ref(x_79);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PropAsSPredTautology", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__3;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1;
x_5 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mexact tactic failed, ", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" is not an SPred tautology", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("from_tautology", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__9;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__4;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2;
x_5 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1;
x_6 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0;
x_7 = l_Lean_Name_mkStr6(x_6, x_5, x_4, x_3, x_2, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1;
x_13 = 0;
x_14 = lean_box(0);
lean_inc_ref(x_7);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_12, x_13, x_14, x_7, x_8, x_9, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_20 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_21 = l_Lean_Elab_Tactic_elabTermEnsuringType(x_2, x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_28);
lean_dec_ref(x_1);
x_29 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2;
x_30 = lean_box(0);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_30);
lean_ctor_set(x_21, 0, x_25);
lean_inc_ref(x_21);
x_31 = l_Lean_Expr_const___override(x_29, x_21);
lean_inc_ref(x_26);
x_32 = l_Lean_Expr_app___override(x_31, x_26);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_inc_ref(x_7);
x_34 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_33, x_13, x_14, x_7, x_8, x_9, x_10, x_24);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
x_38 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4;
lean_inc_ref(x_21);
x_39 = l_Lean_Expr_const___override(x_38, x_21);
lean_inc_ref(x_26);
lean_inc(x_17);
x_40 = l_Lean_mkApp3(x_39, x_17, x_26, x_36);
x_41 = lean_box(0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_42 = l_Lean_Meta_synthInstance_x3f(x_40, x_41, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_21);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_23);
lean_dec(x_17);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6;
x_46 = l_Lean_MessageData_ofSyntax(x_2);
lean_ctor_set_tag(x_34, 7);
lean_ctor_set(x_34, 1, x_46);
lean_ctor_set(x_34, 0, x_45);
x_47 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_47);
lean_ctor_set(x_15, 0, x_34);
x_48 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_15, x_7, x_8, x_9, x_10, x_44);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_48;
}
else
{
uint8_t x_49; 
lean_free_object(x_34);
lean_free_object(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_42, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
lean_dec(x_43);
x_52 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10;
x_53 = l_Lean_Expr_const___override(x_52, x_21);
x_54 = l_Lean_mkApp6(x_53, x_26, x_17, x_27, x_28, x_51, x_23);
lean_ctor_set(x_42, 0, x_54);
return x_42;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_42, 1);
lean_inc(x_55);
lean_dec(x_42);
x_56 = lean_ctor_get(x_43, 0);
lean_inc(x_56);
lean_dec(x_43);
x_57 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10;
x_58 = l_Lean_Expr_const___override(x_57, x_21);
x_59 = l_Lean_mkApp6(x_58, x_26, x_17, x_27, x_28, x_56, x_23);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_free_object(x_34);
lean_dec_ref(x_21);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_23);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_42);
if (x_61 == 0)
{
return x_42;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_42, 0);
x_63 = lean_ctor_get(x_42, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_42);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_34, 0);
x_66 = lean_ctor_get(x_34, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_34);
x_67 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4;
lean_inc_ref(x_21);
x_68 = l_Lean_Expr_const___override(x_67, x_21);
lean_inc_ref(x_26);
lean_inc(x_17);
x_69 = l_Lean_mkApp3(x_68, x_17, x_26, x_65);
x_70 = lean_box(0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_71 = l_Lean_Meta_synthInstance_x3f(x_69, x_70, x_7, x_8, x_9, x_10, x_66);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec_ref(x_21);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_23);
lean_dec(x_17);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6;
x_75 = l_Lean_MessageData_ofSyntax(x_2);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_77);
lean_ctor_set(x_15, 0, x_76);
x_78 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_15, x_7, x_8, x_9, x_10, x_73);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_free_object(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_79 = lean_ctor_get(x_71, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_80 = x_71;
} else {
 lean_dec_ref(x_71);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_72, 0);
lean_inc(x_81);
lean_dec(x_72);
x_82 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10;
x_83 = l_Lean_Expr_const___override(x_82, x_21);
x_84 = l_Lean_mkApp6(x_83, x_26, x_17, x_27, x_28, x_81, x_23);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_21);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_23);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_86 = lean_ctor_get(x_71, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_71, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_88 = x_71;
} else {
 lean_dec_ref(x_71);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_90 = lean_ctor_get(x_21, 0);
x_91 = lean_ctor_get(x_21, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_21);
x_92 = lean_ctor_get(x_1, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_95);
lean_dec_ref(x_1);
x_96 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2;
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_92);
lean_ctor_set(x_98, 1, x_97);
lean_inc_ref(x_98);
x_99 = l_Lean_Expr_const___override(x_96, x_98);
lean_inc_ref(x_93);
x_100 = l_Lean_Expr_app___override(x_99, x_93);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
lean_inc_ref(x_7);
x_102 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_101, x_13, x_14, x_7, x_8, x_9, x_10, x_91);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
x_106 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4;
lean_inc_ref(x_98);
x_107 = l_Lean_Expr_const___override(x_106, x_98);
lean_inc_ref(x_93);
lean_inc(x_17);
x_108 = l_Lean_mkApp3(x_107, x_17, x_93, x_103);
x_109 = lean_box(0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_110 = l_Lean_Meta_synthInstance_x3f(x_108, x_109, x_7, x_8, x_9, x_10, x_104);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_98);
lean_dec_ref(x_95);
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec(x_90);
lean_dec(x_17);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec_ref(x_110);
x_113 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6;
x_114 = l_Lean_MessageData_ofSyntax(x_2);
if (lean_is_scalar(x_105)) {
 x_115 = lean_alloc_ctor(7, 2, 0);
} else {
 x_115 = x_105;
 lean_ctor_set_tag(x_115, 7);
}
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_116);
lean_ctor_set(x_15, 0, x_115);
x_117 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_15, x_7, x_8, x_9, x_10, x_112);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_105);
lean_free_object(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_118 = lean_ctor_get(x_110, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_119 = x_110;
} else {
 lean_dec_ref(x_110);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_111, 0);
lean_inc(x_120);
lean_dec(x_111);
x_121 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10;
x_122 = l_Lean_Expr_const___override(x_121, x_98);
x_123 = l_Lean_mkApp6(x_122, x_93, x_17, x_94, x_95, x_120, x_90);
if (lean_is_scalar(x_119)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_119;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_118);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_105);
lean_dec_ref(x_98);
lean_dec_ref(x_95);
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec(x_90);
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_125 = lean_ctor_get(x_110, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_110, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_127 = x_110;
} else {
 lean_dec_ref(x_110);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
else
{
lean_free_object(x_15);
lean_dec(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_21;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_15, 0);
x_130 = lean_ctor_get(x_15, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_15);
lean_inc(x_129);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_129);
x_132 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_133 = l_Lean_Elab_Tactic_elabTermEnsuringType(x_2, x_131, x_132, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_130);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_1, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_138);
x_139 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_139);
x_140 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_140);
lean_dec_ref(x_1);
x_141 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2;
x_142 = lean_box(0);
if (lean_is_scalar(x_136)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_136;
 lean_ctor_set_tag(x_143, 1);
}
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_142);
lean_inc_ref(x_143);
x_144 = l_Lean_Expr_const___override(x_141, x_143);
lean_inc_ref(x_138);
x_145 = l_Lean_Expr_app___override(x_144, x_138);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
lean_inc_ref(x_7);
x_147 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_146, x_13, x_14, x_7, x_8, x_9, x_10, x_135);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_151 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4;
lean_inc_ref(x_143);
x_152 = l_Lean_Expr_const___override(x_151, x_143);
lean_inc_ref(x_138);
lean_inc(x_129);
x_153 = l_Lean_mkApp3(x_152, x_129, x_138, x_148);
x_154 = lean_box(0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_155 = l_Lean_Meta_synthInstance_x3f(x_153, x_154, x_7, x_8, x_9, x_10, x_149);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec_ref(x_143);
lean_dec_ref(x_140);
lean_dec_ref(x_139);
lean_dec_ref(x_138);
lean_dec(x_134);
lean_dec(x_129);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec_ref(x_155);
x_158 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6;
x_159 = l_Lean_MessageData_ofSyntax(x_2);
if (lean_is_scalar(x_150)) {
 x_160 = lean_alloc_ctor(7, 2, 0);
} else {
 x_160 = x_150;
 lean_ctor_set_tag(x_160, 7);
}
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8;
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_162, x_7, x_8, x_9, x_10, x_157);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_150);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_164 = lean_ctor_get(x_155, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_165 = x_155;
} else {
 lean_dec_ref(x_155);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_156, 0);
lean_inc(x_166);
lean_dec(x_156);
x_167 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10;
x_168 = l_Lean_Expr_const___override(x_167, x_143);
x_169 = l_Lean_mkApp6(x_168, x_138, x_129, x_139, x_140, x_166, x_134);
if (lean_is_scalar(x_165)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_165;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_164);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_150);
lean_dec_ref(x_143);
lean_dec_ref(x_140);
lean_dec_ref(x_139);
lean_dec_ref(x_138);
lean_dec(x_134);
lean_dec(x_129);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_171 = lean_ctor_get(x_155, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_155, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_173 = x_155;
} else {
 lean_dec_ref(x_155);
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
lean_dec(x_129);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_133;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not in proof mode", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_24; 
lean_inc(x_1);
x_24 = l_Lean_MVarId_getType(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_25, x_8, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(x_28);
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1;
x_32 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_31, x_7, x_8, x_9, x_10, x_29);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
lean_inc(x_33);
x_34 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(x_33, x_2, x_7, x_8, x_9, x_10, x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_4);
x_37 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
x_12 = x_38;
x_13 = x_4;
x_14 = x_7;
x_15 = x_8;
x_16 = x_9;
x_17 = x_10;
x_18 = x_39;
goto block_23;
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_dec_ref(x_34);
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
lean_dec(x_35);
x_12 = x_45;
x_13 = x_4;
x_14 = x_7;
x_15 = x_8;
x_16 = x_9;
x_17 = x_10;
x_18 = x_44;
goto block_23;
}
}
else
{
uint8_t x_46; 
lean_dec(x_33);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_34);
if (x_46 == 0)
{
return x_34;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_34, 0);
x_48 = lean_ctor_get(x_34, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_34);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_24);
if (x_50 == 0)
{
return x_24;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_24, 0);
x_52 = lean_ctor_get(x_24, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_24);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
block_23:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0___redArg(x_1, x_12, x_15, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_box(0);
x_22 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_21, x_13, x_14, x_15, x_16, x_17, x_20);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
return x_22;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mexact", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__2;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__1;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
lean_inc(x_15);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0), 11, 2);
lean_closure_set(x_19, 0, x_15);
lean_closure_set(x_19, 1, x_18);
x_20 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_15, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ProofMode", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabMExact", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__2;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3;
x_5 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__1;
x_6 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__0;
x_7 = l_Lean_Name_mkStr6(x_6, x_5, x_4, x_3, x_2, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__0;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__4;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_Do_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__0);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__1);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__2);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__3);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__4 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__4);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__5 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__5);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__6);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__7 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__7);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__8);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__9 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__9);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__10);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__11 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__11);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__12 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact___closed__12);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__0);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__1);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__2);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__3 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__3);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__4);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__5 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__5);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__6);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__7 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__7);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__8);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__9 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__9);
l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10 = _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure___closed__10);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__0);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___lam__0___closed__1);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__0 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__0);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__1 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__1);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__2 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__2);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___closed__3);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__0 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__0);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__1 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__1);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__2 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__2);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__3);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__4 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1___closed__4);
if (builtin) {res = l_Lean_Elab_Tactic_Do_ProofMode_elabMExact___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExact__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
