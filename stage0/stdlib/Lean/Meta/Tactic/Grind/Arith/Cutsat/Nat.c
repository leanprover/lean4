// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
// Imports: Init.Data.Int.OfNat Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Simp.Arith.Nat.Basic Lean.Meta.Tactic.Grind.Arith.Cutsat.Foreign Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
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
lean_object* l_Lean_Meta_isInstHAddInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHMulNat___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__0;
static lean_object* l_Int_OfNat_toExpr___closed__8;
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__1;
static lean_object* l_Int_OfNat_toIntDvd_x3f___closed__3;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__4;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__6;
LEAN_EXPORT lean_object* l_Int_OfNat_toIntEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__2;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkForeignVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__3;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__5;
static lean_object* l_Int_OfNat_toExpr___closed__7;
lean_object* l_Lean_mkIntDiv(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__0;
static lean_object* l_Int_OfNat_toOfNatExpr___closed__1;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__6;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_mkIntMod(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__4;
static lean_object* l_Int_OfNat_toExpr___closed__11;
lean_object* l_Lean_mkIntMul(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__19;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__3;
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1;
LEAN_EXPORT lean_object* l_Int_OfNat_instToExprExpr;
uint8_t lean_int_dec_le(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__0;
static lean_object* l_Int_OfNat_toExpr___closed__17;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__5;
static lean_object* l_Int_OfNat_toExpr___closed__4;
static lean_object* l_Int_OfNat_toExpr___closed__18;
LEAN_EXPORT lean_object* l_Int_OfNat_ofDenoteAsIntExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_instToExprExpr___closed__0;
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toIntDvd_x3f___closed__4;
lean_object* l_Lean_Meta_isInstHMulInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_toOfNatExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__13;
static lean_object* l_Int_OfNat_toExpr___closed__10;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getForeignVars___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__1;
uint8_t l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_alreadyInternalized_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toIntDvd_x3f___closed__6;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_isInstLENat___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__1;
static lean_object* l_Int_OfNat_toExpr___closed__9;
static lean_object* l_Int_OfNat_toOfNatExpr___closed__8;
static lean_object* l_Int_OfNat_toOfNatExpr___closed__13;
LEAN_EXPORT lean_object* l_Int_OfNat_toIntDvd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__16;
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__4;
lean_object* l_Lean_mkIntLit(lean_object*);
static lean_object* l_Int_OfNat_toIntLe_x3f___closed__1;
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__12;
lean_object* l_Int_Linear_Expr_norm(lean_object*);
lean_object* l_Lean_mkIntNatCast(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__14;
static lean_object* l_Int_OfNat_toIntLe_x3f___closed__2;
static lean_object* l_Int_OfNat_toIntLe_x3f___closed__0;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__12;
static lean_object* l_Int_OfNat_toExpr___closed__6;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__2;
lean_object* l_Lean_Meta_isInstHAddNat___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__9;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr_go(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__11;
static lean_object* l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHModNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__7;
lean_object* l_Int_toNat(lean_object*);
static lean_object* l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5;
static lean_object* l_Int_OfNat_toIntDvd_x3f___closed__5;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__2;
static lean_object* l_Int_OfNat_toIntDvd_x3f___closed__0;
static lean_object* l_Int_OfNat_toOfNatExpr___closed__3;
static lean_object* l_Int_OfNat_toOfNatExpr___closed__10;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_instToExprExpr___lam__0(lean_object*);
lean_object* l_Lean_Meta_isInstDvdNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_instToExprExpr___closed__1;
static lean_object* l_Int_OfNat_toIntDvd_x3f___closed__1;
static lean_object* l_Int_OfNat_toExpr___closed__20;
lean_object* lean_int_neg(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__0;
lean_object* l_Lean_Meta_isInstHDivInt___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__15;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__3;
static lean_object* l_Int_OfNat_toIntDvd_x3f___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__5;
lean_object* l_Lean_Meta_isInstHDivNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_toIntLe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHModInt___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0;
LEAN_EXPORT lean_object* l_Int_OfNat_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Int_OfNat_toExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OfNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expr", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("num", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Int_OfNat_toExpr___closed__3;
x_2 = l_Int_OfNat_toExpr___closed__2;
x_3 = l_Int_OfNat_toExpr___closed__1;
x_4 = l_Int_OfNat_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Int_OfNat_toExpr___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("var", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Int_OfNat_toExpr___closed__6;
x_2 = l_Int_OfNat_toExpr___closed__2;
x_3 = l_Int_OfNat_toExpr___closed__1;
x_4 = l_Int_OfNat_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Int_OfNat_toExpr___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Int_OfNat_toExpr___closed__9;
x_2 = l_Int_OfNat_toExpr___closed__2;
x_3 = l_Int_OfNat_toExpr___closed__1;
x_4 = l_Int_OfNat_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Int_OfNat_toExpr___closed__10;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mul", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Int_OfNat_toExpr___closed__12;
x_2 = l_Int_OfNat_toExpr___closed__2;
x_3 = l_Int_OfNat_toExpr___closed__1;
x_4 = l_Int_OfNat_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Int_OfNat_toExpr___closed__13;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("div", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Int_OfNat_toExpr___closed__15;
x_2 = l_Int_OfNat_toExpr___closed__2;
x_3 = l_Int_OfNat_toExpr___closed__1;
x_4 = l_Int_OfNat_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Int_OfNat_toExpr___closed__16;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mod", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Int_OfNat_toExpr___closed__18;
x_2 = l_Int_OfNat_toExpr___closed__2;
x_3 = l_Int_OfNat_toExpr___closed__1;
x_4 = l_Int_OfNat_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Int_OfNat_toExpr___closed__19;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_toExpr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Int_OfNat_toExpr___closed__5;
x_4 = l_Lean_mkNatLit(x_2);
x_5 = l_Lean_Expr_app___override(x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Int_OfNat_toExpr___closed__8;
x_8 = l_Lean_mkNatLit(x_6);
x_9 = l_Lean_Expr_app___override(x_7, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Int_OfNat_toExpr___closed__11;
x_13 = l_Int_OfNat_toExpr(x_10);
x_14 = l_Int_OfNat_toExpr(x_11);
x_15 = l_Lean_mkAppB(x_12, x_13, x_14);
return x_15;
}
case 3:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Int_OfNat_toExpr___closed__14;
x_19 = l_Int_OfNat_toExpr(x_16);
x_20 = l_Int_OfNat_toExpr(x_17);
x_21 = l_Lean_mkAppB(x_18, x_19, x_20);
return x_21;
}
case 4:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Int_OfNat_toExpr___closed__17;
x_25 = l_Int_OfNat_toExpr(x_22);
x_26 = l_Int_OfNat_toExpr(x_23);
x_27 = l_Lean_mkAppB(x_24, x_25, x_26);
return x_27;
}
default: 
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = l_Int_OfNat_toExpr___closed__20;
x_31 = l_Int_OfNat_toExpr(x_28);
x_32 = l_Int_OfNat_toExpr(x_29);
x_33 = l_Lean_mkAppB(x_30, x_31, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_instToExprExpr___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_OfNat_toExpr(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_OfNat_instToExprExpr___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Int_OfNat_toExpr___closed__2;
x_2 = l_Int_OfNat_toExpr___closed__1;
x_3 = l_Int_OfNat_toExpr___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Int_OfNat_instToExprExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Int_OfNat_instToExprExpr___closed__0;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_instToExprExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Int_OfNat_instToExprExpr___lam__0), 1, 0);
x_2 = l_Int_OfNat_instToExprExpr___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_nat_to_int(x_3);
x_5 = l_Lean_mkIntLit(x_4);
lean_dec(x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = l_Lean_instInhabitedExpr;
x_9 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_1);
x_10 = l_outOfBounds___redArg(x_8);
x_11 = l_Lean_mkIntNatCast(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_PersistentArray_get_x21___redArg(x_8, x_1, x_6);
lean_dec(x_6);
x_13 = l_Lean_mkIntNatCast(x_12);
return x_13;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_1);
x_16 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_14);
x_17 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_15);
x_18 = l_Lean_mkIntAdd(x_16, x_17);
return x_18;
}
case 3:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
lean_inc(x_1);
x_21 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_19);
x_22 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_20);
x_23 = l_Lean_mkIntMul(x_21, x_22);
return x_23;
}
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_dec(x_2);
lean_inc(x_1);
x_26 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_24);
x_27 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_25);
x_28 = l_Lean_mkIntDiv(x_26, x_27);
return x_28;
}
default: 
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_dec(x_2);
lean_inc(x_1);
x_31 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_29);
x_32 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_30);
x_33 = l_Lean_mkIntMod(x_31, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_2);
x_6 = l_Lean_Meta_Grind_shareCommon___redArg(x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_1, x_2, x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Int_OfNat_Expr_denoteAsIntExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_OfNat_toOfNatExpr___closed__0;
x_2 = l_Int_OfNat_toExpr___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_OfNat_toOfNatExpr___closed__3;
x_2 = l_Int_OfNat_toOfNatExpr___closed__2;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HDiv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hDiv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_OfNat_toOfNatExpr___closed__6;
x_2 = l_Int_OfNat_toOfNatExpr___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_OfNat_toOfNatExpr___closed__9;
x_2 = l_Int_OfNat_toOfNatExpr___closed__8;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_OfNat_toOfNatExpr___closed__12;
x_2 = l_Int_OfNat_toOfNatExpr___closed__11;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_toOfNatExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_inc(x_1);
x_35 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Expr_cleanupAnnotations(x_36);
x_39 = l_Lean_Expr_isApp(x_38);
if (x_39 == 0)
{
lean_dec(x_38);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_37;
goto block_34;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
x_41 = l_Lean_Expr_appFnCleanup___redArg(x_38);
x_42 = l_Lean_Expr_isApp(x_41);
if (x_42 == 0)
{
lean_dec(x_41);
lean_dec(x_40);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_37;
goto block_34;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
x_44 = l_Lean_Expr_appFnCleanup___redArg(x_41);
x_45 = l_Lean_Expr_isApp(x_44);
if (x_45 == 0)
{
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_40);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_37;
goto block_34;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
x_47 = l_Lean_Expr_appFnCleanup___redArg(x_44);
x_48 = l_Int_OfNat_toOfNatExpr___closed__1;
x_49 = l_Lean_Expr_isConstOf(x_47, x_48);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = l_Lean_Expr_isApp(x_47);
if (x_50 == 0)
{
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_40);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_37;
goto block_34;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = l_Lean_Expr_appFnCleanup___redArg(x_47);
x_52 = l_Lean_Expr_isApp(x_51);
if (x_52 == 0)
{
lean_dec(x_51);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_40);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_37;
goto block_34;
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = l_Lean_Expr_appFnCleanup___redArg(x_51);
x_54 = l_Lean_Expr_isApp(x_53);
if (x_54 == 0)
{
lean_dec(x_53);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_40);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_37;
goto block_34;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = l_Lean_Expr_appFnCleanup___redArg(x_53);
x_56 = l_Int_OfNat_toOfNatExpr___closed__4;
x_57 = l_Lean_Expr_isConstOf(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Int_OfNat_toOfNatExpr___closed__7;
x_59 = l_Lean_Expr_isConstOf(x_55, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = l_Int_OfNat_toOfNatExpr___closed__10;
x_61 = l_Lean_Expr_isConstOf(x_55, x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = l_Int_OfNat_toOfNatExpr___closed__13;
x_63 = l_Lean_Expr_isConstOf(x_55, x_62);
lean_dec(x_55);
if (x_63 == 0)
{
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_40);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_37;
goto block_34;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = l_Lean_Meta_isInstHAddNat___redArg(x_46, x_7, x_37);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_43);
lean_dec(x_40);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_67;
goto block_34;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_1);
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_69 = l_Int_OfNat_toOfNatExpr(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_68);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
x_73 = l_Int_OfNat_toOfNatExpr(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_72);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 0);
lean_ctor_set_tag(x_69, 2);
lean_ctor_set(x_69, 1, x_75);
lean_ctor_set(x_73, 0, x_69);
return x_73;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_73, 0);
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_73);
lean_ctor_set_tag(x_69, 2);
lean_ctor_set(x_69, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_69);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
lean_free_object(x_69);
lean_dec(x_71);
return x_73;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_69, 0);
x_80 = lean_ctor_get(x_69, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_69);
x_81 = l_Int_OfNat_toOfNatExpr(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_79);
lean_ctor_set(x_85, 1, x_82);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
else
{
lean_dec(x_79);
return x_81;
}
}
}
else
{
lean_dec(x_40);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_69;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_55);
x_87 = l_Lean_Meta_isInstHMulNat___redArg(x_46, x_7, x_37);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_43);
lean_dec(x_40);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_90;
goto block_34;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_1);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_dec(x_87);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_92 = l_Int_OfNat_toOfNatExpr(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_91);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_ctor_get(x_92, 1);
x_96 = l_Int_OfNat_toOfNatExpr(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_95);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_96, 0);
lean_ctor_set_tag(x_92, 3);
lean_ctor_set(x_92, 1, x_98);
lean_ctor_set(x_96, 0, x_92);
return x_96;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_96, 0);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_96);
lean_ctor_set_tag(x_92, 3);
lean_ctor_set(x_92, 1, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_92);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
lean_free_object(x_92);
lean_dec(x_94);
return x_96;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_92, 0);
x_103 = lean_ctor_get(x_92, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_92);
x_104 = l_Int_OfNat_toOfNatExpr(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
x_108 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_108, 0, x_102);
lean_ctor_set(x_108, 1, x_105);
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_106);
return x_109;
}
else
{
lean_dec(x_102);
return x_104;
}
}
}
else
{
lean_dec(x_40);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_92;
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_55);
x_110 = l_Lean_Meta_isInstHDivNat___redArg(x_46, x_7, x_37);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; 
lean_dec(x_43);
lean_dec(x_40);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_113;
goto block_34;
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_1);
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
lean_dec(x_110);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_115 = l_Int_OfNat_toOfNatExpr(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_114);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = l_Int_OfNat_toOfNatExpr(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_118);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_119, 0);
lean_ctor_set_tag(x_115, 4);
lean_ctor_set(x_115, 1, x_121);
lean_ctor_set(x_119, 0, x_115);
return x_119;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_119, 0);
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_119);
lean_ctor_set_tag(x_115, 4);
lean_ctor_set(x_115, 1, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_115);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
else
{
lean_free_object(x_115);
lean_dec(x_117);
return x_119;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_115, 0);
x_126 = lean_ctor_get(x_115, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_115);
x_127 = l_Int_OfNat_toOfNatExpr(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
x_131 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_131, 0, x_125);
lean_ctor_set(x_131, 1, x_128);
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_130;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_129);
return x_132;
}
else
{
lean_dec(x_125);
return x_127;
}
}
}
else
{
lean_dec(x_40);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_115;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_55);
x_133 = l_Lean_Meta_isInstHModNat___redArg(x_46, x_7, x_37);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_unbox(x_134);
lean_dec(x_134);
if (x_135 == 0)
{
lean_object* x_136; 
lean_dec(x_43);
lean_dec(x_40);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_136;
goto block_34;
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_1);
x_137 = lean_ctor_get(x_133, 1);
lean_inc(x_137);
lean_dec(x_133);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_138 = l_Int_OfNat_toOfNatExpr(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_137);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = lean_ctor_get(x_138, 1);
x_142 = l_Int_OfNat_toOfNatExpr(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_141);
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_142, 0);
lean_ctor_set_tag(x_138, 5);
lean_ctor_set(x_138, 1, x_144);
lean_ctor_set(x_142, 0, x_138);
return x_142;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_142, 0);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_142);
lean_ctor_set_tag(x_138, 5);
lean_ctor_set(x_138, 1, x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_138);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
else
{
lean_free_object(x_138);
lean_dec(x_140);
return x_142;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_138, 0);
x_149 = lean_ctor_get(x_138, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_138);
x_150 = l_Int_OfNat_toOfNatExpr(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
x_154 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set(x_154, 1, x_151);
if (lean_is_scalar(x_153)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_153;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_152);
return x_155;
}
else
{
lean_dec(x_148);
return x_150;
}
}
}
else
{
lean_dec(x_40);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_138;
}
}
}
}
}
}
}
else
{
lean_object* x_156; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_40);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_156 = l_Lean_Meta_getNatValue_x3f(x_1, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_158;
goto block_34;
}
else
{
uint8_t x_159; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_156);
if (x_159 == 0)
{
lean_object* x_160; uint8_t x_161; 
x_160 = lean_ctor_get(x_156, 0);
lean_dec(x_160);
x_161 = !lean_is_exclusive(x_157);
if (x_161 == 0)
{
lean_ctor_set_tag(x_157, 0);
return x_156;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_157, 0);
lean_inc(x_162);
lean_dec(x_157);
x_163 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_156, 0, x_163);
return x_156;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_164 = lean_ctor_get(x_156, 1);
lean_inc(x_164);
lean_dec(x_156);
x_165 = lean_ctor_get(x_157, 0);
lean_inc(x_165);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 x_166 = x_157;
} else {
 lean_dec_ref(x_157);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 1, 0);
} else {
 x_167 = x_166;
 lean_ctor_set_tag(x_167, 0);
}
lean_ctor_set(x_167, 0, x_165);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_164);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_156);
if (x_169 == 0)
{
return x_156;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_156, 0);
x_171 = lean_ctor_get(x_156, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_156);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
}
}
block_34:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_mkForeignVar(x_11, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
static lean_object* _init_l_Int_OfNat_toIntLe_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toIntLe_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toIntLe_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_OfNat_toIntLe_x3f___closed__1;
x_2 = l_Int_OfNat_toIntLe_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_toIntLe_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Expr_cleanupAnnotations(x_1);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_27 = l_Int_OfNat_toIntLe_x3f___closed__2;
x_28 = l_Lean_Expr_isConstOf(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = l_Lean_Meta_isInstLENat___redArg(x_23, x_7, x_10);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_dec(x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_39 = l_Int_OfNat_toOfNatExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Int_OfNat_toOfNatExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_40);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_39);
if (x_56 == 0)
{
return x_39;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_39, 0);
x_58 = lean_ctor_get(x_39, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_39);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
static lean_object* _init_l_Int_OfNat_toIntDvd_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Dvd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toIntDvd_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dvd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toIntDvd_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_OfNat_toIntDvd_x3f___closed__1;
x_2 = l_Int_OfNat_toIntDvd_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toIntDvd_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("non-linear divisibility constraint found", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toIntDvd_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_OfNat_toIntDvd_x3f___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_OfNat_toIntDvd_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toIntDvd_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_OfNat_toIntDvd_x3f___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_toIntDvd_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_19; uint8_t x_20; 
lean_inc(x_1);
x_19 = l_Lean_Expr_cleanupAnnotations(x_1);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_31 = l_Int_OfNat_toIntDvd_x3f___closed__2;
x_32 = l_Lean_Expr_isConstOf(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Lean_Meta_isInstDvdNat___redArg(x_27, x_7, x_10);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_33, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_33, 0, x_38);
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_dec(x_33);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_Meta_getNatValue_x3f(x_24, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_24);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_21);
lean_dec(x_2);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_47, sizeof(void*)*6 + 11);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_15 = x_49;
goto block_18;
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_46, 1);
x_52 = lean_ctor_get(x_46, 0);
lean_dec(x_52);
x_53 = l_Int_OfNat_toIntDvd_x3f___closed__4;
x_54 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_46, 7);
lean_ctor_set(x_46, 1, x_54);
lean_ctor_set(x_46, 0, x_53);
x_55 = l_Int_OfNat_toIntDvd_x3f___closed__6;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_46);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Meta_Grind_reportIssue(x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_15 = x_58;
goto block_18;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_dec(x_46);
x_60 = l_Int_OfNat_toIntDvd_x3f___closed__4;
x_61 = l_Lean_indentExpr(x_1);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Int_OfNat_toIntDvd_x3f___closed__6;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_Meta_Grind_reportIssue(x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_59);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_15 = x_66;
goto block_18;
}
}
}
else
{
lean_object* x_67; uint8_t x_68; 
lean_dec(x_1);
x_67 = lean_ctor_get(x_43, 1);
lean_inc(x_67);
lean_dec(x_43);
x_68 = !lean_is_exclusive(x_44);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_44, 0);
x_70 = l_Int_OfNat_toOfNatExpr(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_67);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_44, 0, x_73);
lean_ctor_set(x_70, 0, x_44);
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_70);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_44, 0, x_76);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_44);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_free_object(x_44);
lean_dec(x_69);
x_78 = !lean_is_exclusive(x_70);
if (x_78 == 0)
{
return x_70;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_70, 0);
x_80 = lean_ctor_get(x_70, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_70);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_44, 0);
lean_inc(x_82);
lean_dec(x_44);
x_83 = l_Int_OfNat_toOfNatExpr(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_67);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_84);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_85);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_82);
x_90 = lean_ctor_get(x_83, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_83, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_92 = x_83;
} else {
 lean_dec_ref(x_83);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_43);
if (x_94 == 0)
{
return x_43;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_43, 0);
x_96 = lean_ctor_get(x_43, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_43);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_toIntEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Int_OfNat_toOfNatExpr(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Int_OfNat_toOfNatExpr(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("NatCast", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("natCast", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__1;
x_2 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instNatCastInt", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_ofDenoteAsIntExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_91; uint8_t x_92; 
lean_inc(x_1);
x_15 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_91 = l_Lean_Expr_cleanupAnnotations(x_16);
x_92 = l_Lean_Expr_isApp(x_91);
if (x_92 == 0)
{
lean_dec(x_91);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_90;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
x_94 = l_Lean_Expr_appFnCleanup___redArg(x_91);
x_95 = l_Lean_Expr_isApp(x_94);
if (x_95 == 0)
{
lean_dec(x_94);
lean_dec(x_93);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_90;
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
x_97 = l_Lean_Expr_appFnCleanup___redArg(x_94);
x_98 = l_Lean_Expr_isApp(x_97);
if (x_98 == 0)
{
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_93);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_90;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
x_100 = l_Lean_Expr_appFnCleanup___redArg(x_97);
x_101 = l_Int_OfNat_toOfNatExpr___closed__1;
x_102 = l_Lean_Expr_isConstOf(x_100, x_101);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = l_Lean_Expr_isApp(x_100);
if (x_103 == 0)
{
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_96);
lean_dec(x_93);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_90;
}
else
{
lean_object* x_104; uint8_t x_105; 
x_104 = l_Lean_Expr_appFnCleanup___redArg(x_100);
x_105 = l_Lean_Expr_isApp(x_104);
if (x_105 == 0)
{
lean_dec(x_104);
lean_dec(x_99);
lean_dec(x_96);
lean_dec(x_93);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_90;
}
else
{
lean_object* x_106; uint8_t x_107; 
x_106 = l_Lean_Expr_appFnCleanup___redArg(x_104);
x_107 = l_Lean_Expr_isApp(x_106);
if (x_107 == 0)
{
lean_dec(x_106);
lean_dec(x_99);
lean_dec(x_96);
lean_dec(x_93);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_90;
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = l_Lean_Expr_appFnCleanup___redArg(x_106);
x_109 = l_Int_OfNat_toOfNatExpr___closed__4;
x_110 = l_Lean_Expr_isConstOf(x_108, x_109);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = l_Int_OfNat_toOfNatExpr___closed__7;
x_112 = l_Lean_Expr_isConstOf(x_108, x_111);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = l_Int_OfNat_toOfNatExpr___closed__10;
x_114 = l_Lean_Expr_isConstOf(x_108, x_113);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = l_Int_OfNat_toOfNatExpr___closed__13;
x_116 = l_Lean_Expr_isConstOf(x_108, x_115);
lean_dec(x_108);
if (x_116 == 0)
{
lean_dec(x_99);
lean_dec(x_96);
lean_dec(x_93);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_90;
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
lean_dec(x_1);
x_117 = l_Lean_Meta_isInstHAddInt___redArg(x_99, x_7, x_17);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_unbox(x_118);
lean_dec(x_118);
if (x_119 == 0)
{
uint8_t x_120; 
lean_dec(x_96);
lean_dec(x_93);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_117);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_117, 0);
lean_dec(x_121);
x_122 = lean_box(0);
lean_ctor_set(x_117, 0, x_122);
return x_117;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_117, 1);
lean_inc(x_123);
lean_dec(x_117);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_117, 1);
lean_inc(x_126);
lean_dec(x_117);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_127 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_96, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_dec(x_93);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_127;
}
else
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_127);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_127, 1);
x_131 = lean_ctor_get(x_127, 0);
lean_dec(x_131);
x_132 = lean_ctor_get(x_128, 0);
lean_inc(x_132);
lean_dec(x_128);
x_133 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_93, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_130);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 0)
{
lean_dec(x_132);
lean_free_object(x_127);
return x_133;
}
else
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_133);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_133, 0);
lean_dec(x_136);
x_137 = !lean_is_exclusive(x_134);
if (x_137 == 0)
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_134, 0);
lean_ctor_set_tag(x_127, 2);
lean_ctor_set(x_127, 1, x_138);
lean_ctor_set(x_127, 0, x_132);
lean_ctor_set(x_134, 0, x_127);
return x_133;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_134, 0);
lean_inc(x_139);
lean_dec(x_134);
lean_ctor_set_tag(x_127, 2);
lean_ctor_set(x_127, 1, x_139);
lean_ctor_set(x_127, 0, x_132);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_127);
lean_ctor_set(x_133, 0, x_140);
return x_133;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_141 = lean_ctor_get(x_133, 1);
lean_inc(x_141);
lean_dec(x_133);
x_142 = lean_ctor_get(x_134, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_143 = x_134;
} else {
 lean_dec_ref(x_134);
 x_143 = lean_box(0);
}
lean_ctor_set_tag(x_127, 2);
lean_ctor_set(x_127, 1, x_142);
lean_ctor_set(x_127, 0, x_132);
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 1, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_127);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_141);
return x_145;
}
}
}
else
{
lean_dec(x_132);
lean_free_object(x_127);
return x_133;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_127, 1);
lean_inc(x_146);
lean_dec(x_127);
x_147 = lean_ctor_get(x_128, 0);
lean_inc(x_147);
lean_dec(x_128);
x_148 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_93, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_146);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 0)
{
lean_dec(x_147);
return x_148;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_151 = x_148;
} else {
 lean_dec_ref(x_148);
 x_151 = lean_box(0);
}
x_152 = lean_ctor_get(x_149, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_153 = x_149;
} else {
 lean_dec_ref(x_149);
 x_153 = lean_box(0);
}
x_154 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_154, 0, x_147);
lean_ctor_set(x_154, 1, x_152);
if (lean_is_scalar(x_153)) {
 x_155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_155 = x_153;
}
lean_ctor_set(x_155, 0, x_154);
if (lean_is_scalar(x_151)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_151;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_150);
return x_156;
}
}
else
{
lean_dec(x_147);
return x_148;
}
}
}
}
else
{
lean_dec(x_93);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_127;
}
}
}
}
else
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; 
lean_dec(x_108);
lean_dec(x_1);
x_157 = l_Lean_Meta_isInstHMulInt___redArg(x_99, x_7, x_17);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_unbox(x_158);
lean_dec(x_158);
if (x_159 == 0)
{
uint8_t x_160; 
lean_dec(x_96);
lean_dec(x_93);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_160 = !lean_is_exclusive(x_157);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_157, 0);
lean_dec(x_161);
x_162 = lean_box(0);
lean_ctor_set(x_157, 0, x_162);
return x_157;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_157, 1);
lean_inc(x_163);
lean_dec(x_157);
x_164 = lean_box(0);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_157, 1);
lean_inc(x_166);
lean_dec(x_157);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_167 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_96, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_166);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
if (lean_obj_tag(x_168) == 0)
{
lean_dec(x_93);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_167;
}
else
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_167);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_167, 1);
x_171 = lean_ctor_get(x_167, 0);
lean_dec(x_171);
x_172 = lean_ctor_get(x_168, 0);
lean_inc(x_172);
lean_dec(x_168);
x_173 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_93, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_170);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
if (lean_obj_tag(x_174) == 0)
{
lean_dec(x_172);
lean_free_object(x_167);
return x_173;
}
else
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_173);
if (x_175 == 0)
{
lean_object* x_176; uint8_t x_177; 
x_176 = lean_ctor_get(x_173, 0);
lean_dec(x_176);
x_177 = !lean_is_exclusive(x_174);
if (x_177 == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_174, 0);
lean_ctor_set_tag(x_167, 3);
lean_ctor_set(x_167, 1, x_178);
lean_ctor_set(x_167, 0, x_172);
lean_ctor_set(x_174, 0, x_167);
return x_173;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_174, 0);
lean_inc(x_179);
lean_dec(x_174);
lean_ctor_set_tag(x_167, 3);
lean_ctor_set(x_167, 1, x_179);
lean_ctor_set(x_167, 0, x_172);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_167);
lean_ctor_set(x_173, 0, x_180);
return x_173;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_173, 1);
lean_inc(x_181);
lean_dec(x_173);
x_182 = lean_ctor_get(x_174, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_183 = x_174;
} else {
 lean_dec_ref(x_174);
 x_183 = lean_box(0);
}
lean_ctor_set_tag(x_167, 3);
lean_ctor_set(x_167, 1, x_182);
lean_ctor_set(x_167, 0, x_172);
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 1, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_167);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_181);
return x_185;
}
}
}
else
{
lean_dec(x_172);
lean_free_object(x_167);
return x_173;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_167, 1);
lean_inc(x_186);
lean_dec(x_167);
x_187 = lean_ctor_get(x_168, 0);
lean_inc(x_187);
lean_dec(x_168);
x_188 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_93, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_186);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
if (lean_obj_tag(x_189) == 0)
{
lean_dec(x_187);
return x_188;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_191 = x_188;
} else {
 lean_dec_ref(x_188);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_189, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 x_193 = x_189;
} else {
 lean_dec_ref(x_189);
 x_193 = lean_box(0);
}
x_194 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_194, 0, x_187);
lean_ctor_set(x_194, 1, x_192);
if (lean_is_scalar(x_193)) {
 x_195 = lean_alloc_ctor(1, 1, 0);
} else {
 x_195 = x_193;
}
lean_ctor_set(x_195, 0, x_194);
if (lean_is_scalar(x_191)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_191;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_190);
return x_196;
}
}
else
{
lean_dec(x_187);
return x_188;
}
}
}
}
else
{
lean_dec(x_93);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_167;
}
}
}
}
else
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_dec(x_108);
lean_dec(x_1);
x_197 = l_Lean_Meta_isInstHDivInt___redArg(x_99, x_7, x_17);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_unbox(x_198);
lean_dec(x_198);
if (x_199 == 0)
{
uint8_t x_200; 
lean_dec(x_96);
lean_dec(x_93);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_197, 0);
lean_dec(x_201);
x_202 = lean_box(0);
lean_ctor_set(x_197, 0, x_202);
return x_197;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_197, 1);
lean_inc(x_203);
lean_dec(x_197);
x_204 = lean_box(0);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_197, 1);
lean_inc(x_206);
lean_dec(x_197);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_207 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_96, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
lean_dec(x_93);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_207;
}
else
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_207);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_ctor_get(x_207, 1);
x_211 = lean_ctor_get(x_207, 0);
lean_dec(x_211);
x_212 = lean_ctor_get(x_208, 0);
lean_inc(x_212);
lean_dec(x_208);
x_213 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_93, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_210);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
if (lean_obj_tag(x_214) == 0)
{
lean_dec(x_212);
lean_free_object(x_207);
return x_213;
}
else
{
uint8_t x_215; 
x_215 = !lean_is_exclusive(x_213);
if (x_215 == 0)
{
lean_object* x_216; uint8_t x_217; 
x_216 = lean_ctor_get(x_213, 0);
lean_dec(x_216);
x_217 = !lean_is_exclusive(x_214);
if (x_217 == 0)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_214, 0);
lean_ctor_set_tag(x_207, 4);
lean_ctor_set(x_207, 1, x_218);
lean_ctor_set(x_207, 0, x_212);
lean_ctor_set(x_214, 0, x_207);
return x_213;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_214, 0);
lean_inc(x_219);
lean_dec(x_214);
lean_ctor_set_tag(x_207, 4);
lean_ctor_set(x_207, 1, x_219);
lean_ctor_set(x_207, 0, x_212);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_207);
lean_ctor_set(x_213, 0, x_220);
return x_213;
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_221 = lean_ctor_get(x_213, 1);
lean_inc(x_221);
lean_dec(x_213);
x_222 = lean_ctor_get(x_214, 0);
lean_inc(x_222);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 x_223 = x_214;
} else {
 lean_dec_ref(x_214);
 x_223 = lean_box(0);
}
lean_ctor_set_tag(x_207, 4);
lean_ctor_set(x_207, 1, x_222);
lean_ctor_set(x_207, 0, x_212);
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 1, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_207);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_221);
return x_225;
}
}
}
else
{
lean_dec(x_212);
lean_free_object(x_207);
return x_213;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_207, 1);
lean_inc(x_226);
lean_dec(x_207);
x_227 = lean_ctor_get(x_208, 0);
lean_inc(x_227);
lean_dec(x_208);
x_228 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_93, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_226);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
if (lean_obj_tag(x_229) == 0)
{
lean_dec(x_227);
return x_228;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_231 = x_228;
} else {
 lean_dec_ref(x_228);
 x_231 = lean_box(0);
}
x_232 = lean_ctor_get(x_229, 0);
lean_inc(x_232);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 x_233 = x_229;
} else {
 lean_dec_ref(x_229);
 x_233 = lean_box(0);
}
x_234 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_234, 0, x_227);
lean_ctor_set(x_234, 1, x_232);
if (lean_is_scalar(x_233)) {
 x_235 = lean_alloc_ctor(1, 1, 0);
} else {
 x_235 = x_233;
}
lean_ctor_set(x_235, 0, x_234);
if (lean_is_scalar(x_231)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_231;
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_230);
return x_236;
}
}
else
{
lean_dec(x_227);
return x_228;
}
}
}
}
else
{
lean_dec(x_93);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_207;
}
}
}
}
else
{
lean_object* x_237; lean_object* x_238; uint8_t x_239; 
lean_dec(x_108);
lean_dec(x_1);
x_237 = l_Lean_Meta_isInstHModInt___redArg(x_99, x_7, x_17);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_unbox(x_238);
lean_dec(x_238);
if (x_239 == 0)
{
uint8_t x_240; 
lean_dec(x_96);
lean_dec(x_93);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_240 = !lean_is_exclusive(x_237);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_ctor_get(x_237, 0);
lean_dec(x_241);
x_242 = lean_box(0);
lean_ctor_set(x_237, 0, x_242);
return x_237;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_237, 1);
lean_inc(x_243);
lean_dec(x_237);
x_244 = lean_box(0);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_237, 1);
lean_inc(x_246);
lean_dec(x_237);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_247 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_96, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_246);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_dec(x_93);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_247;
}
else
{
uint8_t x_249; 
x_249 = !lean_is_exclusive(x_247);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = lean_ctor_get(x_247, 1);
x_251 = lean_ctor_get(x_247, 0);
lean_dec(x_251);
x_252 = lean_ctor_get(x_248, 0);
lean_inc(x_252);
lean_dec(x_248);
x_253 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_93, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_250);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
if (lean_obj_tag(x_254) == 0)
{
lean_dec(x_252);
lean_free_object(x_247);
return x_253;
}
else
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_253);
if (x_255 == 0)
{
lean_object* x_256; uint8_t x_257; 
x_256 = lean_ctor_get(x_253, 0);
lean_dec(x_256);
x_257 = !lean_is_exclusive(x_254);
if (x_257 == 0)
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_254, 0);
lean_ctor_set_tag(x_247, 5);
lean_ctor_set(x_247, 1, x_258);
lean_ctor_set(x_247, 0, x_252);
lean_ctor_set(x_254, 0, x_247);
return x_253;
}
else
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_254, 0);
lean_inc(x_259);
lean_dec(x_254);
lean_ctor_set_tag(x_247, 5);
lean_ctor_set(x_247, 1, x_259);
lean_ctor_set(x_247, 0, x_252);
x_260 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_260, 0, x_247);
lean_ctor_set(x_253, 0, x_260);
return x_253;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_261 = lean_ctor_get(x_253, 1);
lean_inc(x_261);
lean_dec(x_253);
x_262 = lean_ctor_get(x_254, 0);
lean_inc(x_262);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 x_263 = x_254;
} else {
 lean_dec_ref(x_254);
 x_263 = lean_box(0);
}
lean_ctor_set_tag(x_247, 5);
lean_ctor_set(x_247, 1, x_262);
lean_ctor_set(x_247, 0, x_252);
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(1, 1, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_247);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_261);
return x_265;
}
}
}
else
{
lean_dec(x_252);
lean_free_object(x_247);
return x_253;
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_247, 1);
lean_inc(x_266);
lean_dec(x_247);
x_267 = lean_ctor_get(x_248, 0);
lean_inc(x_267);
lean_dec(x_248);
x_268 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_93, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_266);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
if (lean_obj_tag(x_269) == 0)
{
lean_dec(x_267);
return x_268;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_271 = x_268;
} else {
 lean_dec_ref(x_268);
 x_271 = lean_box(0);
}
x_272 = lean_ctor_get(x_269, 0);
lean_inc(x_272);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 x_273 = x_269;
} else {
 lean_dec_ref(x_269);
 x_273 = lean_box(0);
}
x_274 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_274, 0, x_267);
lean_ctor_set(x_274, 1, x_272);
if (lean_is_scalar(x_273)) {
 x_275 = lean_alloc_ctor(1, 1, 0);
} else {
 x_275 = x_273;
}
lean_ctor_set(x_275, 0, x_274);
if (lean_is_scalar(x_271)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_271;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_270);
return x_276;
}
}
else
{
lean_dec(x_267);
return x_268;
}
}
}
}
else
{
lean_dec(x_93);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_247;
}
}
}
}
}
}
}
else
{
lean_object* x_277; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_96);
lean_dec(x_93);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_277 = l_Lean_Meta_getIntValue_x3f(x_1, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
if (lean_obj_tag(x_278) == 0)
{
uint8_t x_279; 
x_279 = !lean_is_exclusive(x_277);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_ctor_get(x_277, 0);
lean_dec(x_280);
x_281 = lean_box(0);
lean_ctor_set(x_277, 0, x_281);
return x_277;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_277, 1);
lean_inc(x_282);
lean_dec(x_277);
x_283 = lean_box(0);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
else
{
uint8_t x_285; 
x_285 = !lean_is_exclusive(x_277);
if (x_285 == 0)
{
lean_object* x_286; uint8_t x_287; 
x_286 = lean_ctor_get(x_277, 0);
lean_dec(x_286);
x_287 = !lean_is_exclusive(x_278);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_288 = lean_ctor_get(x_278, 0);
x_289 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5;
x_290 = lean_int_dec_le(x_289, x_288);
if (x_290 == 0)
{
lean_object* x_291; 
lean_free_object(x_278);
lean_dec(x_288);
x_291 = lean_box(0);
lean_ctor_set(x_277, 0, x_291);
return x_277;
}
else
{
lean_object* x_292; lean_object* x_293; 
x_292 = l_Int_toNat(x_288);
lean_dec(x_288);
x_293 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_278, 0, x_293);
return x_277;
}
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_294 = lean_ctor_get(x_278, 0);
lean_inc(x_294);
lean_dec(x_278);
x_295 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5;
x_296 = lean_int_dec_le(x_295, x_294);
if (x_296 == 0)
{
lean_object* x_297; 
lean_dec(x_294);
x_297 = lean_box(0);
lean_ctor_set(x_277, 0, x_297);
return x_277;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = l_Int_toNat(x_294);
lean_dec(x_294);
x_299 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_299, 0, x_298);
x_300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_277, 0, x_300);
return x_277;
}
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_301 = lean_ctor_get(x_277, 1);
lean_inc(x_301);
lean_dec(x_277);
x_302 = lean_ctor_get(x_278, 0);
lean_inc(x_302);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 x_303 = x_278;
} else {
 lean_dec_ref(x_278);
 x_303 = lean_box(0);
}
x_304 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5;
x_305 = lean_int_dec_le(x_304, x_302);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; 
lean_dec(x_303);
lean_dec(x_302);
x_306 = lean_box(0);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_301);
return x_307;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_308 = l_Int_toNat(x_302);
lean_dec(x_302);
x_309 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_309, 0, x_308);
if (lean_is_scalar(x_303)) {
 x_310 = lean_alloc_ctor(1, 1, 0);
} else {
 x_310 = x_303;
}
lean_ctor_set(x_310, 0, x_309);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_301);
return x_311;
}
}
}
}
else
{
uint8_t x_312; 
x_312 = !lean_is_exclusive(x_277);
if (x_312 == 0)
{
return x_277;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_277, 0);
x_314 = lean_ctor_get(x_277, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_277);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
return x_315;
}
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_90:
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_23, x_17);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = l_Lean_Expr_cleanupAnnotations(x_28);
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_dec(x_30);
lean_free_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_29;
goto block_14;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_34 = l_Lean_Expr_isApp(x_33);
if (x_34 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_free_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_29;
goto block_14;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
x_36 = l_Lean_Expr_appFnCleanup___redArg(x_33);
x_37 = l_Lean_Expr_isApp(x_36);
if (x_37 == 0)
{
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_32);
lean_free_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_29;
goto block_14;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = l_Lean_Expr_appFnCleanup___redArg(x_36);
x_39 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2;
x_40 = l_Lean_Expr_isConstOf(x_38, x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_dec(x_35);
lean_dec(x_32);
lean_free_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_29;
goto block_14;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = l_Lean_Expr_cleanupAnnotations(x_35);
x_42 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__4;
x_43 = l_Lean_Expr_isConstOf(x_41, x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_44 = lean_box(0);
lean_ctor_set(x_26, 0, x_44);
return x_26;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_free_object(x_26);
x_45 = lean_box(0);
x_46 = l_Lean_Meta_Grind_Arith_Cutsat_mkForeignVar(x_32, x_45, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_29);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_46, 0);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_46);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_46);
if (x_56 == 0)
{
return x_46;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_46, 0);
x_58 = lean_ctor_get(x_46, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_46);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_26, 0);
x_61 = lean_ctor_get(x_26, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_26);
x_62 = l_Lean_Expr_cleanupAnnotations(x_60);
x_63 = l_Lean_Expr_isApp(x_62);
if (x_63 == 0)
{
lean_dec(x_62);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_61;
goto block_14;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
x_65 = l_Lean_Expr_appFnCleanup___redArg(x_62);
x_66 = l_Lean_Expr_isApp(x_65);
if (x_66 == 0)
{
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_61;
goto block_14;
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
x_68 = l_Lean_Expr_appFnCleanup___redArg(x_65);
x_69 = l_Lean_Expr_isApp(x_68);
if (x_69 == 0)
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_61;
goto block_14;
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = l_Lean_Expr_appFnCleanup___redArg(x_68);
x_71 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2;
x_72 = l_Lean_Expr_isConstOf(x_70, x_71);
lean_dec(x_70);
if (x_72 == 0)
{
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_61;
goto block_14;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = l_Lean_Expr_cleanupAnnotations(x_67);
x_74 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__4;
x_75 = l_Lean_Expr_isConstOf(x_73, x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_64);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_61);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_box(0);
x_79 = l_Lean_Meta_Grind_Arith_Cutsat_mkForeignVar(x_64, x_78, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_61);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_80);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_82;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_79, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_79, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_88 = x_79;
} else {
 lean_dec_ref(x_79);
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
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information", 157, 157);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__5;
x_2 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__2;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__6;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_2, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 2);
x_15 = lean_ctor_get(x_8, 3);
x_16 = lean_ctor_get(x_8, 4);
x_17 = lean_ctor_get(x_8, 5);
x_18 = lean_ctor_get(x_8, 6);
x_19 = lean_ctor_get(x_8, 7);
x_20 = lean_ctor_get(x_8, 8);
x_21 = lean_ctor_get(x_8, 9);
x_22 = lean_ctor_get(x_8, 10);
x_23 = lean_ctor_get(x_8, 11);
x_24 = lean_ctor_get(x_8, 12);
x_25 = lean_nat_dec_eq(x_15, x_16);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2;
x_27 = l_Lean_Expr_isAppOf(x_1, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Int_OfNat_toOfNatExpr___closed__1;
x_29 = l_Lean_Expr_isAppOf(x_1, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_15, x_30);
lean_dec(x_15);
lean_ctor_set(x_8, 3, x_31);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_32 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
x_42 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_40);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = lean_box(0);
x_47 = l_Lean_Meta_Grind_Arith_Cutsat_getForeignVars___redArg(x_46, x_2, x_45);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_41);
x_51 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_49, x_41, x_5, x_50);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_55 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_53, x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0;
lean_inc(x_56);
lean_ctor_set_tag(x_51, 3);
lean_ctor_set(x_51, 1, x_56);
lean_ctor_set(x_51, 0, x_58);
x_59 = l_Int_Linear_Expr_norm(x_51);
lean_dec(x_51);
lean_ctor_set_tag(x_47, 4);
lean_ctor_set(x_47, 1, x_56);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_42, 1, x_47);
lean_ctor_set(x_42, 0, x_59);
x_60 = lean_grind_cutsat_assert_le(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_57);
return x_60;
}
else
{
uint8_t x_61; 
lean_free_object(x_51);
lean_free_object(x_47);
lean_free_object(x_42);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_55);
if (x_61 == 0)
{
return x_55;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_55, 0);
x_63 = lean_ctor_get(x_55, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_55);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_51, 0);
x_66 = lean_ctor_get(x_51, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_51);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_67 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_65, x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0;
lean_inc(x_68);
x_71 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
x_72 = l_Int_Linear_Expr_norm(x_71);
lean_dec(x_71);
lean_ctor_set_tag(x_47, 4);
lean_ctor_set(x_47, 1, x_68);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_42, 1, x_47);
lean_ctor_set(x_42, 0, x_72);
x_73 = lean_grind_cutsat_assert_le(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_69);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_free_object(x_47);
lean_free_object(x_42);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_ctor_get(x_67, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_67, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_76 = x_67;
} else {
 lean_dec_ref(x_67);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_47, 0);
x_79 = lean_ctor_get(x_47, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_47);
lean_inc(x_41);
x_80 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_78, x_41, x_5, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_84 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_81, x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0;
lean_inc(x_85);
if (lean_is_scalar(x_83)) {
 x_88 = lean_alloc_ctor(3, 2, 0);
} else {
 x_88 = x_83;
 lean_ctor_set_tag(x_88, 3);
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
x_89 = l_Int_Linear_Expr_norm(x_88);
lean_dec(x_88);
x_90 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_90, 0, x_41);
lean_ctor_set(x_90, 1, x_85);
lean_ctor_set(x_42, 1, x_90);
lean_ctor_set(x_42, 0, x_89);
x_91 = lean_grind_cutsat_assert_le(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_86);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_83);
lean_free_object(x_42);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_ctor_get(x_84, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_84, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_94 = x_84;
} else {
 lean_dec_ref(x_84);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_96 = lean_ctor_get(x_42, 0);
x_97 = lean_ctor_get(x_42, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_42);
x_98 = lean_box(0);
x_99 = l_Lean_Meta_Grind_Arith_Cutsat_getForeignVars___redArg(x_98, x_2, x_97);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
lean_inc(x_41);
x_103 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_100, x_41, x_5, x_101);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_106 = x_103;
} else {
 lean_dec_ref(x_103);
 x_106 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_107 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_104, x_96, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_105);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0;
lean_inc(x_108);
if (lean_is_scalar(x_106)) {
 x_111 = lean_alloc_ctor(3, 2, 0);
} else {
 x_111 = x_106;
 lean_ctor_set_tag(x_111, 3);
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
x_112 = l_Int_Linear_Expr_norm(x_111);
lean_dec(x_111);
if (lean_is_scalar(x_102)) {
 x_113 = lean_alloc_ctor(4, 2, 0);
} else {
 x_113 = x_102;
 lean_ctor_set_tag(x_113, 4);
}
lean_ctor_set(x_113, 0, x_41);
lean_ctor_set(x_113, 1, x_108);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_grind_cutsat_assert_le(x_114, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_109);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_106);
lean_dec(x_102);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_116 = lean_ctor_get(x_107, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_107, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_118 = x_107;
} else {
 lean_dec_ref(x_107);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_32);
if (x_120 == 0)
{
return x_32;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_32, 0);
x_122 = lean_ctor_get(x_32, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_32);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_free_object(x_8);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_10);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_free_object(x_8);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_10);
return x_127;
}
}
else
{
lean_object* x_128; 
lean_free_object(x_8);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_17, x_10);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; uint8_t x_144; 
x_129 = lean_ctor_get(x_8, 0);
x_130 = lean_ctor_get(x_8, 1);
x_131 = lean_ctor_get(x_8, 2);
x_132 = lean_ctor_get(x_8, 3);
x_133 = lean_ctor_get(x_8, 4);
x_134 = lean_ctor_get(x_8, 5);
x_135 = lean_ctor_get(x_8, 6);
x_136 = lean_ctor_get(x_8, 7);
x_137 = lean_ctor_get(x_8, 8);
x_138 = lean_ctor_get(x_8, 9);
x_139 = lean_ctor_get(x_8, 10);
x_140 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_141 = lean_ctor_get(x_8, 11);
x_142 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_143 = lean_ctor_get(x_8, 12);
lean_inc(x_143);
lean_inc(x_141);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_8);
x_144 = lean_nat_dec_eq(x_132, x_133);
if (x_144 == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2;
x_146 = l_Lean_Expr_isAppOf(x_1, x_145);
if (x_146 == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = l_Int_OfNat_toOfNatExpr___closed__1;
x_148 = l_Lean_Expr_isAppOf(x_1, x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_unsigned_to_nat(1u);
x_150 = lean_nat_add(x_132, x_149);
lean_dec(x_132);
x_151 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_151, 0, x_129);
lean_ctor_set(x_151, 1, x_130);
lean_ctor_set(x_151, 2, x_131);
lean_ctor_set(x_151, 3, x_150);
lean_ctor_set(x_151, 4, x_133);
lean_ctor_set(x_151, 5, x_134);
lean_ctor_set(x_151, 6, x_135);
lean_ctor_set(x_151, 7, x_136);
lean_ctor_set(x_151, 8, x_137);
lean_ctor_set(x_151, 9, x_138);
lean_ctor_set(x_151, 10, x_139);
lean_ctor_set(x_151, 11, x_141);
lean_ctor_set(x_151, 12, x_143);
lean_ctor_set_uint8(x_151, sizeof(void*)*13, x_140);
lean_ctor_set_uint8(x_151, sizeof(void*)*13 + 1, x_142);
lean_inc(x_9);
lean_inc(x_151);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_152 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_151, x_9, x_10);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_151);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_155 = x_152;
} else {
 lean_dec_ref(x_152);
 x_155 = lean_box(0);
}
x_156 = lean_box(0);
if (lean_is_scalar(x_155)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_155;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_154);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_158 = lean_ctor_get(x_152, 1);
lean_inc(x_158);
lean_dec(x_152);
x_159 = lean_ctor_get(x_153, 0);
lean_inc(x_159);
lean_dec(x_153);
x_160 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_158);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_163 = x_160;
} else {
 lean_dec_ref(x_160);
 x_163 = lean_box(0);
}
x_164 = lean_box(0);
x_165 = l_Lean_Meta_Grind_Arith_Cutsat_getForeignVars___redArg(x_164, x_2, x_162);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_168 = x_165;
} else {
 lean_dec_ref(x_165);
 x_168 = lean_box(0);
}
lean_inc(x_159);
x_169 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_166, x_159, x_5, x_167);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_172 = x_169;
} else {
 lean_dec_ref(x_169);
 x_172 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_151);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_173 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_170, x_161, x_2, x_3, x_4, x_5, x_6, x_7, x_151, x_9, x_171);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0;
lean_inc(x_174);
if (lean_is_scalar(x_172)) {
 x_177 = lean_alloc_ctor(3, 2, 0);
} else {
 x_177 = x_172;
 lean_ctor_set_tag(x_177, 3);
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_174);
x_178 = l_Int_Linear_Expr_norm(x_177);
lean_dec(x_177);
if (lean_is_scalar(x_168)) {
 x_179 = lean_alloc_ctor(4, 2, 0);
} else {
 x_179 = x_168;
 lean_ctor_set_tag(x_179, 4);
}
lean_ctor_set(x_179, 0, x_159);
lean_ctor_set(x_179, 1, x_174);
if (lean_is_scalar(x_163)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_163;
}
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_grind_cutsat_assert_le(x_180, x_2, x_3, x_4, x_5, x_6, x_7, x_151, x_9, x_175);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_172);
lean_dec(x_168);
lean_dec(x_163);
lean_dec(x_159);
lean_dec(x_151);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_182 = lean_ctor_get(x_173, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_173, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_184 = x_173;
} else {
 lean_dec_ref(x_173);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_151);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_186 = lean_ctor_get(x_152, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_152, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_188 = x_152;
} else {
 lean_dec_ref(x_152);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_190 = lean_box(0);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_10);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_192 = lean_box(0);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_10);
return x_193;
}
}
else
{
lean_object* x_194; 
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_194 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_134, x_10);
return x_194;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Expr_cleanupAnnotations(x_1);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = x_11;
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = x_11;
goto block_15;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = x_11;
goto block_15;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2;
x_26 = l_Lean_Expr_isConstOf(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = x_11;
goto block_15;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = l_Lean_Expr_cleanupAnnotations(x_21);
x_28 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__4;
x_29 = l_Lean_Expr_isConstOf(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_11);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Int_OfNat_toOfNatExpr___closed__1;
x_33 = l_Lean_Expr_isAppOf(x_18, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_3, x_11);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
x_38 = lean_ctor_get(x_36, 4);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_alreadyInternalized_spec__0___redArg(x_38, x_18);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_free_object(x_34);
x_40 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_mkForeignVar(x_18, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1;
x_45 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2;
lean_inc(x_2);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_2);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_2);
x_49 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_grind_cutsat_assert_le(x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
return x_41;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_41, 0);
x_54 = lean_ctor_get(x_41, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_41);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_box(0);
lean_ctor_set(x_34, 0, x_56);
return x_34;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_34, 0);
x_58 = lean_ctor_get(x_34, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_34);
x_59 = lean_ctor_get(x_57, 4);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_alreadyInternalized_spec__0___redArg(x_59, x_18);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_62 = l_Lean_Meta_Grind_Arith_Cutsat_mkForeignVar(x_18, x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1;
x_66 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2;
lean_inc(x_2);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_2);
lean_ctor_set(x_67, 2, x_66);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_2);
x_70 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_grind_cutsat_assert_le(x_71, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_64);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_ctor_get(x_62, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_62, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_75 = x_62;
} else {
 lean_dec_ref(x_62);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_58);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_11);
return x_80;
}
}
}
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Foreign(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_OfNat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Foreign(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_OfNat_toExpr___closed__0 = _init_l_Int_OfNat_toExpr___closed__0();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__0);
l_Int_OfNat_toExpr___closed__1 = _init_l_Int_OfNat_toExpr___closed__1();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__1);
l_Int_OfNat_toExpr___closed__2 = _init_l_Int_OfNat_toExpr___closed__2();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__2);
l_Int_OfNat_toExpr___closed__3 = _init_l_Int_OfNat_toExpr___closed__3();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__3);
l_Int_OfNat_toExpr___closed__4 = _init_l_Int_OfNat_toExpr___closed__4();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__4);
l_Int_OfNat_toExpr___closed__5 = _init_l_Int_OfNat_toExpr___closed__5();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__5);
l_Int_OfNat_toExpr___closed__6 = _init_l_Int_OfNat_toExpr___closed__6();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__6);
l_Int_OfNat_toExpr___closed__7 = _init_l_Int_OfNat_toExpr___closed__7();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__7);
l_Int_OfNat_toExpr___closed__8 = _init_l_Int_OfNat_toExpr___closed__8();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__8);
l_Int_OfNat_toExpr___closed__9 = _init_l_Int_OfNat_toExpr___closed__9();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__9);
l_Int_OfNat_toExpr___closed__10 = _init_l_Int_OfNat_toExpr___closed__10();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__10);
l_Int_OfNat_toExpr___closed__11 = _init_l_Int_OfNat_toExpr___closed__11();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__11);
l_Int_OfNat_toExpr___closed__12 = _init_l_Int_OfNat_toExpr___closed__12();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__12);
l_Int_OfNat_toExpr___closed__13 = _init_l_Int_OfNat_toExpr___closed__13();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__13);
l_Int_OfNat_toExpr___closed__14 = _init_l_Int_OfNat_toExpr___closed__14();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__14);
l_Int_OfNat_toExpr___closed__15 = _init_l_Int_OfNat_toExpr___closed__15();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__15);
l_Int_OfNat_toExpr___closed__16 = _init_l_Int_OfNat_toExpr___closed__16();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__16);
l_Int_OfNat_toExpr___closed__17 = _init_l_Int_OfNat_toExpr___closed__17();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__17);
l_Int_OfNat_toExpr___closed__18 = _init_l_Int_OfNat_toExpr___closed__18();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__18);
l_Int_OfNat_toExpr___closed__19 = _init_l_Int_OfNat_toExpr___closed__19();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__19);
l_Int_OfNat_toExpr___closed__20 = _init_l_Int_OfNat_toExpr___closed__20();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__20);
l_Int_OfNat_instToExprExpr___closed__0 = _init_l_Int_OfNat_instToExprExpr___closed__0();
lean_mark_persistent(l_Int_OfNat_instToExprExpr___closed__0);
l_Int_OfNat_instToExprExpr___closed__1 = _init_l_Int_OfNat_instToExprExpr___closed__1();
lean_mark_persistent(l_Int_OfNat_instToExprExpr___closed__1);
l_Int_OfNat_instToExprExpr = _init_l_Int_OfNat_instToExprExpr();
lean_mark_persistent(l_Int_OfNat_instToExprExpr);
l_Int_OfNat_toOfNatExpr___closed__0 = _init_l_Int_OfNat_toOfNatExpr___closed__0();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__0);
l_Int_OfNat_toOfNatExpr___closed__1 = _init_l_Int_OfNat_toOfNatExpr___closed__1();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__1);
l_Int_OfNat_toOfNatExpr___closed__2 = _init_l_Int_OfNat_toOfNatExpr___closed__2();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__2);
l_Int_OfNat_toOfNatExpr___closed__3 = _init_l_Int_OfNat_toOfNatExpr___closed__3();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__3);
l_Int_OfNat_toOfNatExpr___closed__4 = _init_l_Int_OfNat_toOfNatExpr___closed__4();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__4);
l_Int_OfNat_toOfNatExpr___closed__5 = _init_l_Int_OfNat_toOfNatExpr___closed__5();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__5);
l_Int_OfNat_toOfNatExpr___closed__6 = _init_l_Int_OfNat_toOfNatExpr___closed__6();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__6);
l_Int_OfNat_toOfNatExpr___closed__7 = _init_l_Int_OfNat_toOfNatExpr___closed__7();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__7);
l_Int_OfNat_toOfNatExpr___closed__8 = _init_l_Int_OfNat_toOfNatExpr___closed__8();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__8);
l_Int_OfNat_toOfNatExpr___closed__9 = _init_l_Int_OfNat_toOfNatExpr___closed__9();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__9);
l_Int_OfNat_toOfNatExpr___closed__10 = _init_l_Int_OfNat_toOfNatExpr___closed__10();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__10);
l_Int_OfNat_toOfNatExpr___closed__11 = _init_l_Int_OfNat_toOfNatExpr___closed__11();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__11);
l_Int_OfNat_toOfNatExpr___closed__12 = _init_l_Int_OfNat_toOfNatExpr___closed__12();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__12);
l_Int_OfNat_toOfNatExpr___closed__13 = _init_l_Int_OfNat_toOfNatExpr___closed__13();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__13);
l_Int_OfNat_toIntLe_x3f___closed__0 = _init_l_Int_OfNat_toIntLe_x3f___closed__0();
lean_mark_persistent(l_Int_OfNat_toIntLe_x3f___closed__0);
l_Int_OfNat_toIntLe_x3f___closed__1 = _init_l_Int_OfNat_toIntLe_x3f___closed__1();
lean_mark_persistent(l_Int_OfNat_toIntLe_x3f___closed__1);
l_Int_OfNat_toIntLe_x3f___closed__2 = _init_l_Int_OfNat_toIntLe_x3f___closed__2();
lean_mark_persistent(l_Int_OfNat_toIntLe_x3f___closed__2);
l_Int_OfNat_toIntDvd_x3f___closed__0 = _init_l_Int_OfNat_toIntDvd_x3f___closed__0();
lean_mark_persistent(l_Int_OfNat_toIntDvd_x3f___closed__0);
l_Int_OfNat_toIntDvd_x3f___closed__1 = _init_l_Int_OfNat_toIntDvd_x3f___closed__1();
lean_mark_persistent(l_Int_OfNat_toIntDvd_x3f___closed__1);
l_Int_OfNat_toIntDvd_x3f___closed__2 = _init_l_Int_OfNat_toIntDvd_x3f___closed__2();
lean_mark_persistent(l_Int_OfNat_toIntDvd_x3f___closed__2);
l_Int_OfNat_toIntDvd_x3f___closed__3 = _init_l_Int_OfNat_toIntDvd_x3f___closed__3();
lean_mark_persistent(l_Int_OfNat_toIntDvd_x3f___closed__3);
l_Int_OfNat_toIntDvd_x3f___closed__4 = _init_l_Int_OfNat_toIntDvd_x3f___closed__4();
lean_mark_persistent(l_Int_OfNat_toIntDvd_x3f___closed__4);
l_Int_OfNat_toIntDvd_x3f___closed__5 = _init_l_Int_OfNat_toIntDvd_x3f___closed__5();
lean_mark_persistent(l_Int_OfNat_toIntDvd_x3f___closed__5);
l_Int_OfNat_toIntDvd_x3f___closed__6 = _init_l_Int_OfNat_toIntDvd_x3f___closed__6();
lean_mark_persistent(l_Int_OfNat_toIntDvd_x3f___closed__6);
l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__0 = _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__0();
lean_mark_persistent(l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__0);
l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__1 = _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__1();
lean_mark_persistent(l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__1);
l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2 = _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2();
lean_mark_persistent(l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2);
l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__3 = _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__3();
lean_mark_persistent(l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__3);
l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__4 = _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__4();
lean_mark_persistent(l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__4);
l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5 = _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5();
lean_mark_persistent(l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__0 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__0);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__1);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__2);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__3);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__4);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__5);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
