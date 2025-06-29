// Lean compiler output
// Module: Lean.Util.TestExtern
// Imports: Lean.Elab.SyntheticMVars Lean.Elab.Command Lean.Meta.Tactic.Unfold Lean.Meta.Eval Lean.Compiler.ImplementedByAttr
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
static lean_object* l_elabTestExtern___lam__0___closed__7;
static lean_object* l_testExternCmd___closed__4;
static lean_object* l_testExternCmd___closed__3;
static lean_object* l_testExternCmd___closed__8;
static lean_object* l_testExternCmd___closed__5;
static lean_object* l_elabTestExtern___lam__0___closed__2;
lean_object* l_Lean_Meta_unfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_elabTestExtern___lam__0___closed__0;
static lean_object* l_testExternCmd___closed__2;
static lean_object* l_elabTestExtern___lam__0___closed__11;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_elabTestExtern___lam__0___closed__15;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_elabTestExtern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_implemented_by(lean_object*, lean_object*);
static lean_object* l_elabTestExtern___lam__0___closed__21;
static lean_object* l_elabTestExtern___lam__0___closed__20;
static lean_object* l_elabTestExtern___lam__0___closed__9;
static lean_object* l_elabTestExtern___lam__0___closed__13;
static lean_object* l_elabTestExtern___lam__0___closed__3;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5___redArg(lean_object*);
static lean_object* l_elabTestExtern___lam__0___closed__18;
static lean_object* l_testExternCmd___closed__6;
static lean_object* l_testExternCmd___closed__0;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_elabTestExtern___lam__0___closed__17;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_elabTestExtern___lam__0___closed__4;
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_elabTestExtern___lam__0___closed__14;
static lean_object* l_elabTestExtern___lam__0___closed__16;
static lean_object* l_testExternCmd___closed__7;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_elabTestExtern___lam__0___closed__8;
static lean_object* l_elabTestExtern___lam__0___closed__6;
static lean_object* l_testExternCmd___closed__10;
LEAN_EXPORT lean_object* l_elabTestExtern___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_testExternCmd___closed__1;
static lean_object* l_elabTestExtern___lam__0___closed__10;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAndSynthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_testExternCmd;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_elabTestExtern___lam__0___closed__19;
static lean_object* l_elabTestExtern___lam__0___closed__12;
LEAN_EXPORT lean_object* l_elabTestExtern(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_elabTestExtern___lam__0___closed__1;
static lean_object* l_testExternCmd___closed__9;
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_elabTestExtern___lam__0___closed__5;
LEAN_EXPORT lean_object* l_elabTestExtern___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_testExternCmd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("testExternCmd", 13, 13);
return x_1;
}
}
static lean_object* _init_l_testExternCmd___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_testExternCmd___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_testExternCmd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("andthen", 7, 7);
return x_1;
}
}
static lean_object* _init_l_testExternCmd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_testExternCmd___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_testExternCmd___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("test_extern ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_testExternCmd___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_testExternCmd___closed__4;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_testExternCmd___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_testExternCmd___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_testExternCmd___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_testExternCmd___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_testExternCmd___closed__7;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_testExternCmd___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_testExternCmd___closed__8;
x_2 = l_testExternCmd___closed__5;
x_3 = l_testExternCmd___closed__3;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_testExternCmd___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_testExternCmd___closed__9;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_testExternCmd___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_testExternCmd() {
_start:
{
lean_object* x_1; 
x_1 = l_testExternCmd___closed__10;
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceBool", 10, 10);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_elabTestExtern___lam__0___closed__1;
x_2 = l_elabTestExtern___lam__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_elabTestExtern___lam__0___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabTestExtern___lam__0___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_elabTestExtern___lam__0___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("native implementation did not agree with reference implementation!\n", 67, 67);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabTestExtern___lam__0___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabTestExtern___lam__0___closed__8;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compare the outputs of:\n#eval ", 30, 30);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabTestExtern___lam__0___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n and\n#eval ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabTestExtern___lam__0___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabTestExtern___lam__0___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("test_extern: ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabTestExtern___lam__0___closed__16;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" does not have an @[extern] attribute or @[implemented_by] attribute", 68, 68);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabTestExtern___lam__0___closed__18;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("test_extern: expects a function application", 43, 43);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabTestExtern___lam__0___closed__20;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_elabTestExtern___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Elab_Term_elabTermAndSynthesize(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_74; lean_object* x_82; uint8_t x_83; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_9, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_82 = lean_ctor_get(x_17, 0);
lean_inc(x_82);
lean_dec(x_17);
lean_inc(x_15);
lean_inc(x_82);
x_83 = l_Lean_isExtern(x_82, x_15);
if (x_83 == 0)
{
lean_object* x_84; 
lean_inc(x_15);
x_84 = lean_get_implemented_by(x_82, x_15);
if (lean_obj_tag(x_84) == 0)
{
x_74 = x_83;
goto block_81;
}
else
{
lean_dec(x_84);
x_74 = x_3;
goto block_81;
}
}
else
{
lean_dec(x_82);
goto block_73;
}
block_73:
{
lean_object* x_20; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_20 = l_Lean_Meta_unfold(x_12, x_15, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_23);
lean_inc(x_12);
x_24 = l_Lean_Meta_mkEq(x_12, x_23, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = l_Lean_Meta_mkDecide(x_25, x_6, x_7, x_8, x_9, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_elabTestExtern___lam__0___closed__3;
x_31 = l_Lean_Expr_app___override(x_30, x_28);
x_32 = l_elabTestExtern___lam__0___closed__6;
x_33 = lean_box(1);
x_34 = lean_unbox(x_33);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_35 = l_Lean_Meta_evalExpr___redArg(x_32, x_31, x_34, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_elabTestExtern___lam__0___closed__9;
x_40 = l_elabTestExtern___lam__0___closed__11;
x_41 = l_Lean_MessageData_ofExpr(x_12);
if (lean_is_scalar(x_19)) {
 x_42 = lean_alloc_ctor(7, 2, 0);
} else {
 x_42 = x_19;
 lean_ctor_set_tag(x_42, 7);
}
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_elabTestExtern___lam__0___closed__13;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_MessageData_ofExpr(x_23);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_elabTestExtern___lam__0___closed__15;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_49, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_35);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_35, 0);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set(x_35, 0, x_53);
return x_35;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
lean_dec(x_35);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_35);
if (x_57 == 0)
{
return x_35;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_35, 0);
x_59 = lean_ctor_get(x_35, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_35);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_27);
if (x_61 == 0)
{
return x_27;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_27, 0);
x_63 = lean_ctor_get(x_27, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_27);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_24);
if (x_65 == 0)
{
return x_24;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_24, 0);
x_67 = lean_ctor_get(x_24, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_24);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_20);
if (x_69 == 0)
{
return x_20;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_20, 0);
x_71 = lean_ctor_get(x_20, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_20);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
block_81:
{
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_19);
lean_dec(x_12);
x_75 = l_elabTestExtern___lam__0___closed__17;
x_76 = l_Lean_MessageData_ofName(x_15);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_elabTestExtern___lam__0___closed__19;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_79, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_80;
}
else
{
goto block_73;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_14);
lean_dec(x_12);
x_85 = l_elabTestExtern___lam__0___closed__21;
x_86 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_85, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_86;
}
}
else
{
uint8_t x_87; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_87 = !lean_is_exclusive(x_11);
if (x_87 == 0)
{
return x_11;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_11, 0);
x_89 = lean_ctor_get(x_11, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_11);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
LEAN_EXPORT lean_object* l_elabTestExtern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_testExternCmd___closed__1;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5___redArg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_box(x_6);
x_12 = lean_alloc_closure((void*)(l_elabTestExtern___lam__0___boxed), 10, 3);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
x_13 = l_Lean_Elab_Command_liftTermElabM___redArg(x_12, x_2, x_3, x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_elabTestExtern___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_elabTestExtern___lam__0(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_elabTestExtern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_elabTestExtern(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Unfold(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Eval(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_TestExtern(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_SyntheticMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Unfold(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eval(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ImplementedByAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_testExternCmd___closed__0 = _init_l_testExternCmd___closed__0();
lean_mark_persistent(l_testExternCmd___closed__0);
l_testExternCmd___closed__1 = _init_l_testExternCmd___closed__1();
lean_mark_persistent(l_testExternCmd___closed__1);
l_testExternCmd___closed__2 = _init_l_testExternCmd___closed__2();
lean_mark_persistent(l_testExternCmd___closed__2);
l_testExternCmd___closed__3 = _init_l_testExternCmd___closed__3();
lean_mark_persistent(l_testExternCmd___closed__3);
l_testExternCmd___closed__4 = _init_l_testExternCmd___closed__4();
lean_mark_persistent(l_testExternCmd___closed__4);
l_testExternCmd___closed__5 = _init_l_testExternCmd___closed__5();
lean_mark_persistent(l_testExternCmd___closed__5);
l_testExternCmd___closed__6 = _init_l_testExternCmd___closed__6();
lean_mark_persistent(l_testExternCmd___closed__6);
l_testExternCmd___closed__7 = _init_l_testExternCmd___closed__7();
lean_mark_persistent(l_testExternCmd___closed__7);
l_testExternCmd___closed__8 = _init_l_testExternCmd___closed__8();
lean_mark_persistent(l_testExternCmd___closed__8);
l_testExternCmd___closed__9 = _init_l_testExternCmd___closed__9();
lean_mark_persistent(l_testExternCmd___closed__9);
l_testExternCmd___closed__10 = _init_l_testExternCmd___closed__10();
lean_mark_persistent(l_testExternCmd___closed__10);
l_testExternCmd = _init_l_testExternCmd();
lean_mark_persistent(l_testExternCmd);
l_elabTestExtern___lam__0___closed__0 = _init_l_elabTestExtern___lam__0___closed__0();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__0);
l_elabTestExtern___lam__0___closed__1 = _init_l_elabTestExtern___lam__0___closed__1();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__1);
l_elabTestExtern___lam__0___closed__2 = _init_l_elabTestExtern___lam__0___closed__2();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__2);
l_elabTestExtern___lam__0___closed__3 = _init_l_elabTestExtern___lam__0___closed__3();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__3);
l_elabTestExtern___lam__0___closed__4 = _init_l_elabTestExtern___lam__0___closed__4();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__4);
l_elabTestExtern___lam__0___closed__5 = _init_l_elabTestExtern___lam__0___closed__5();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__5);
l_elabTestExtern___lam__0___closed__6 = _init_l_elabTestExtern___lam__0___closed__6();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__6);
l_elabTestExtern___lam__0___closed__7 = _init_l_elabTestExtern___lam__0___closed__7();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__7);
l_elabTestExtern___lam__0___closed__8 = _init_l_elabTestExtern___lam__0___closed__8();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__8);
l_elabTestExtern___lam__0___closed__9 = _init_l_elabTestExtern___lam__0___closed__9();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__9);
l_elabTestExtern___lam__0___closed__10 = _init_l_elabTestExtern___lam__0___closed__10();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__10);
l_elabTestExtern___lam__0___closed__11 = _init_l_elabTestExtern___lam__0___closed__11();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__11);
l_elabTestExtern___lam__0___closed__12 = _init_l_elabTestExtern___lam__0___closed__12();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__12);
l_elabTestExtern___lam__0___closed__13 = _init_l_elabTestExtern___lam__0___closed__13();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__13);
l_elabTestExtern___lam__0___closed__14 = _init_l_elabTestExtern___lam__0___closed__14();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__14);
l_elabTestExtern___lam__0___closed__15 = _init_l_elabTestExtern___lam__0___closed__15();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__15);
l_elabTestExtern___lam__0___closed__16 = _init_l_elabTestExtern___lam__0___closed__16();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__16);
l_elabTestExtern___lam__0___closed__17 = _init_l_elabTestExtern___lam__0___closed__17();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__17);
l_elabTestExtern___lam__0___closed__18 = _init_l_elabTestExtern___lam__0___closed__18();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__18);
l_elabTestExtern___lam__0___closed__19 = _init_l_elabTestExtern___lam__0___closed__19();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__19);
l_elabTestExtern___lam__0___closed__20 = _init_l_elabTestExtern___lam__0___closed__20();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__20);
l_elabTestExtern___lam__0___closed__21 = _init_l_elabTestExtern___lam__0___closed__21();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__21);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
