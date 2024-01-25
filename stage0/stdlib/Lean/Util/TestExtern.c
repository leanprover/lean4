// Lean compiler output
// Module: Lean.Util.TestExtern
// Imports: Init Lean.Elab.SyntheticMVars Lean.Elab.Command Lean.Meta.Tactic.Unfold Lean.Meta.Eval
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
static lean_object* l_elabTestExtern___lambda__1___closed__23;
static lean_object* l_testExternCmd___closed__11;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_elabTestExtern___lambda__1___closed__14;
LEAN_EXPORT lean_object* l_elabTestExtern___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_testExternCmd___closed__4;
static lean_object* l_elabTestExtern___lambda__1___closed__20;
static lean_object* l_testExternCmd___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1(lean_object*, lean_object*);
static lean_object* l_testExternCmd___closed__8;
static lean_object* l_testExternCmd___closed__5;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_testExternCmd___closed__2;
static lean_object* l_elabTestExtern___lambda__1___closed__15;
static lean_object* l_elabTestExtern___lambda__1___closed__3;
static lean_object* l_elabTestExtern___lambda__1___closed__6;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_elabTestExtern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_elabTestExtern___lambda__1___closed__17;
static lean_object* l_elabTestExtern___lambda__1___closed__18;
static lean_object* l_elabTestExtern___lambda__1___closed__11;
static lean_object* l_elabTestExtern___lambda__1___closed__10;
static lean_object* l_elabTestExtern___lambda__1___closed__8;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1___rarg___closed__1;
static lean_object* l_testExternCmd___closed__6;
lean_object* l_Lean_Meta_evalExpr___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1___rarg___closed__2;
static lean_object* l_elabTestExtern___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1___rarg(lean_object*);
static lean_object* l_elabTestExtern___lambda__1___closed__16;
static lean_object* l_elabTestExtern___lambda__1___closed__25;
static lean_object* l_elabTestExtern___lambda__1___closed__9;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
static lean_object* l_elabTestExtern___lambda__1___closed__21;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_elabTestExtern___lambda__1___closed__2;
static lean_object* l_elabTestExtern___lambda__1___closed__12;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_elabTestExtern___lambda__1___closed__13;
static lean_object* l_elabTestExtern___lambda__1___closed__22;
static lean_object* l_elabTestExtern___lambda__1___closed__24;
static lean_object* l_testExternCmd___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_elabTestExtern___lambda__1___closed__7;
static lean_object* l_testExternCmd___closed__10;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_elabTestExtern___lambda__1___closed__19;
static lean_object* l_testExternCmd___closed__1;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAndSynthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_testExternCmd;
static lean_object* l_elabTestExtern___lambda__1___closed__5;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l_elabTestExtern(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_elabTestExtern___lambda__1___closed__1;
static lean_object* l_testExternCmd___closed__9;
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_elabTestExtern___lambda__1___closed__26;
static lean_object* _init_l_testExternCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("testExternCmd", 13);
return x_1;
}
}
static lean_object* _init_l_testExternCmd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_testExternCmd___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_testExternCmd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("andthen", 7);
return x_1;
}
}
static lean_object* _init_l_testExternCmd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_testExternCmd___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_testExternCmd___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("test_extern ", 12);
return x_1;
}
}
static lean_object* _init_l_testExternCmd___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_testExternCmd___closed__5;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_testExternCmd___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("term", 4);
return x_1;
}
}
static lean_object* _init_l_testExternCmd___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_testExternCmd___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_testExternCmd___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_testExternCmd___closed__8;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_testExternCmd___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_testExternCmd___closed__4;
x_2 = l_testExternCmd___closed__6;
x_3 = l_testExternCmd___closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_testExternCmd___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_testExternCmd___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_testExternCmd___closed__10;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_testExternCmd() {
_start:
{
lean_object* x_1; 
x_1 = l_testExternCmd___closed__11;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("test_extern: expects a function application", 43);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabTestExtern___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("test_extern: ", 13);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabTestExtern___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" does not have an @[extern] attribute", 37);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabTestExtern___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("BEq", 3);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("beq", 3);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_elabTestExtern___lambda__1___closed__7;
x_2 = l_elabTestExtern___lambda__1___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduceBool", 10);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_elabTestExtern___lambda__1___closed__11;
x_2 = l_elabTestExtern___lambda__1___closed__12;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_elabTestExtern___lambda__1___closed__13;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Bool", 4);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_elabTestExtern___lambda__1___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_elabTestExtern___lambda__1___closed__16;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("native implementation did not agree with reference implementation!\n", 67);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabTestExtern___lambda__1___closed__18;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabTestExtern___lambda__1___closed__19;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compare the outputs of:\n#eval ", 30);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabTestExtern___lambda__1___closed__21;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n and\n#eval ", 12);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabTestExtern___lambda__1___closed__23;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_elabTestExtern___lambda__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabTestExtern___lambda__1___closed__25;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_elabTestExtern___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Elab_Term_elabTermAndSynthesize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_getAppFn(x_11);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_8, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_14);
x_19 = l_Lean_isExtern(x_18, x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_11);
x_20 = l_Lean_MessageData_ofName(x_14);
x_21 = l_elabTestExtern___lambda__1___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_elabTestExtern___lambda__1___closed__6;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_25;
}
else
{
lean_object* x_26; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_11);
x_26 = l_Lean_Meta_unfold(x_11, x_14, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_elabTestExtern___lambda__1___closed__10;
lean_inc(x_11);
x_31 = lean_array_push(x_30, x_11);
lean_inc(x_29);
x_32 = lean_array_push(x_31, x_29);
x_33 = l_elabTestExtern___lambda__1___closed__9;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_34 = l_Lean_Meta_mkAppM(x_33, x_32, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_elabTestExtern___lambda__1___closed__14;
x_38 = l_Lean_Expr_app___override(x_37, x_35);
x_39 = l_elabTestExtern___lambda__1___closed__17;
x_40 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_41 = l_Lean_Meta_evalExpr___rarg(x_39, x_38, x_40, x_5, x_6, x_7, x_8, x_36);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l_Lean_MessageData_ofExpr(x_11);
x_46 = l_elabTestExtern___lambda__1___closed__22;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_elabTestExtern___lambda__1___closed__24;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_MessageData_ofExpr(x_29);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_elabTestExtern___lambda__1___closed__26;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_elabTestExtern___lambda__1___closed__20;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_44);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_41);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_41, 0);
lean_dec(x_58);
x_59 = lean_box(0);
lean_ctor_set(x_41, 0, x_59);
return x_41;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_41, 1);
lean_inc(x_60);
lean_dec(x_41);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_41);
if (x_63 == 0)
{
return x_41;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_41, 0);
x_65 = lean_ctor_get(x_41, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_41);
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
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_67 = !lean_is_exclusive(x_34);
if (x_67 == 0)
{
return x_34;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_34, 0);
x_69 = lean_ctor_get(x_34, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_34);
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
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_71 = !lean_is_exclusive(x_26);
if (x_71 == 0)
{
return x_26;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_26, 0);
x_73 = lean_ctor_get(x_26, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_26);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_13);
lean_dec(x_11);
x_75 = l_elabTestExtern___lambda__1___closed__2;
x_76 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_75, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_10);
if (x_77 == 0)
{
return x_10;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_10, 0);
x_79 = lean_ctor_get(x_10, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_10);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
LEAN_EXPORT lean_object* l_elabTestExtern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_testExternCmd___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_closure((void*)(l_elabTestExtern___lambda__1), 9, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_Elab_Command_liftTermElabM___rarg(x_11, x_2, x_3, x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Unfold(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Eval(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_TestExtern(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_testExternCmd___closed__11 = _init_l_testExternCmd___closed__11();
lean_mark_persistent(l_testExternCmd___closed__11);
l_testExternCmd = _init_l_testExternCmd();
lean_mark_persistent(l_testExternCmd);
l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_elabTestExtern___spec__1___rarg___closed__2);
l_elabTestExtern___lambda__1___closed__1 = _init_l_elabTestExtern___lambda__1___closed__1();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__1);
l_elabTestExtern___lambda__1___closed__2 = _init_l_elabTestExtern___lambda__1___closed__2();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__2);
l_elabTestExtern___lambda__1___closed__3 = _init_l_elabTestExtern___lambda__1___closed__3();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__3);
l_elabTestExtern___lambda__1___closed__4 = _init_l_elabTestExtern___lambda__1___closed__4();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__4);
l_elabTestExtern___lambda__1___closed__5 = _init_l_elabTestExtern___lambda__1___closed__5();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__5);
l_elabTestExtern___lambda__1___closed__6 = _init_l_elabTestExtern___lambda__1___closed__6();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__6);
l_elabTestExtern___lambda__1___closed__7 = _init_l_elabTestExtern___lambda__1___closed__7();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__7);
l_elabTestExtern___lambda__1___closed__8 = _init_l_elabTestExtern___lambda__1___closed__8();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__8);
l_elabTestExtern___lambda__1___closed__9 = _init_l_elabTestExtern___lambda__1___closed__9();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__9);
l_elabTestExtern___lambda__1___closed__10 = _init_l_elabTestExtern___lambda__1___closed__10();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__10);
l_elabTestExtern___lambda__1___closed__11 = _init_l_elabTestExtern___lambda__1___closed__11();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__11);
l_elabTestExtern___lambda__1___closed__12 = _init_l_elabTestExtern___lambda__1___closed__12();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__12);
l_elabTestExtern___lambda__1___closed__13 = _init_l_elabTestExtern___lambda__1___closed__13();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__13);
l_elabTestExtern___lambda__1___closed__14 = _init_l_elabTestExtern___lambda__1___closed__14();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__14);
l_elabTestExtern___lambda__1___closed__15 = _init_l_elabTestExtern___lambda__1___closed__15();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__15);
l_elabTestExtern___lambda__1___closed__16 = _init_l_elabTestExtern___lambda__1___closed__16();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__16);
l_elabTestExtern___lambda__1___closed__17 = _init_l_elabTestExtern___lambda__1___closed__17();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__17);
l_elabTestExtern___lambda__1___closed__18 = _init_l_elabTestExtern___lambda__1___closed__18();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__18);
l_elabTestExtern___lambda__1___closed__19 = _init_l_elabTestExtern___lambda__1___closed__19();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__19);
l_elabTestExtern___lambda__1___closed__20 = _init_l_elabTestExtern___lambda__1___closed__20();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__20);
l_elabTestExtern___lambda__1___closed__21 = _init_l_elabTestExtern___lambda__1___closed__21();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__21);
l_elabTestExtern___lambda__1___closed__22 = _init_l_elabTestExtern___lambda__1___closed__22();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__22);
l_elabTestExtern___lambda__1___closed__23 = _init_l_elabTestExtern___lambda__1___closed__23();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__23);
l_elabTestExtern___lambda__1___closed__24 = _init_l_elabTestExtern___lambda__1___closed__24();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__24);
l_elabTestExtern___lambda__1___closed__25 = _init_l_elabTestExtern___lambda__1___closed__25();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__25);
l_elabTestExtern___lambda__1___closed__26 = _init_l_elabTestExtern___lambda__1___closed__26();
lean_mark_persistent(l_elabTestExtern___lambda__1___closed__26);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
