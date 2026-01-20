// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Int.Simp
// Imports: public import Lean.Meta.Tactic.Simp.Arith.Util public import Lean.Meta.Tactic.Simp.Arith.Int.Basic
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
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41;
uint8_t l_Int_Linear_instBEqExpr_beq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3;
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4;
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0;
lean_object* l_Lean_mkIntLE(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23;
uint8_t l_Int_Linear_Poly_isUnsatEq(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15;
uint8_t l_Int_Linear_Poly_isUnsatLe(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12;
lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_denoteExpr___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1;
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntDvd(lean_object*, lean_object*);
lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Simp_Arith_Int_simpEq_x3f_spec__0(lean_object*);
lean_object* l_Lean_mkIntEq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll___boxed(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8;
lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33;
uint8_t l_Int_Linear_Poly_isValidLe(lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Expr_norm(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27___boxed(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11;
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12;
lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
lean_object* l_Int_Linear_Poly_toExpr(lean_object*);
lean_object* lean_nat_abs(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16;
lean_object* l_Int_toNat(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll(lean_object*);
extern lean_object* l_Lean_levelOne;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29;
uint8_t l_Int_Linear_Poly_isValidEq(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37;
lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5;
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5;
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28;
lean_object* l_Int_Linear_Expr_denoteExpr___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5;
extern lean_object* l_Lean_eagerReflBoolTrue;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_nat_abs(x_5);
x_7 = lean_nat_gcd(x_1, x_6);
lean_dec(x_6);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_nat_abs(x_8);
x_11 = lean_nat_gcd(x_1, x_10);
lean_dec(x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_9;
goto _start;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_nat_abs(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_abs(x_4);
x_7 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(x_6, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_Linear_Poly_gcdAll(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_abs(x_5);
x_8 = lean_nat_gcd(x_1, x_7);
lean_dec(x_7);
lean_dec(x_1);
x_1 = x_8;
x_2 = x_6;
goto _start;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(1u);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_nat_abs(x_3);
x_6 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(x_5, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_Linear_Poly_gcdCoeffs_x27(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Simp_Arith_Int_simpEq_x3f_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_get_borrowed(x_1, x_2, x_3);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Linear", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_eq_var_const", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_eq_false_of_divCoeff", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instNegInt", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5;
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_eq_coeff", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_eq", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_eq_var", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("True", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_eq_true", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_eq_false", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_7 = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_9 = x_7;
} else {
 lean_dec_ref(x_7);
 x_9 = lean_box(0);
}
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_14 = x_10;
} else {
 lean_dec_ref(x_10);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
x_18 = l_Lean_instInhabitedExpr;
lean_inc(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_16);
lean_inc(x_13);
lean_inc_ref(x_19);
x_20 = l_Int_Linear_Expr_denoteExpr___redArg(x_19, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_22 = x_20;
} else {
 lean_dec_ref(x_20);
 x_22 = lean_box(0);
}
lean_inc(x_15);
lean_inc_ref(x_19);
x_23 = l_Int_Linear_Expr_denoteExpr___redArg(x_19, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_191; uint8_t x_279; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_25 = x_23;
} else {
 lean_dec_ref(x_23);
 x_25 = lean_box(0);
}
x_26 = l_Lean_mkIntEq(x_21, x_24);
lean_inc(x_15);
lean_inc(x_13);
x_92 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_92, 0, x_13);
lean_ctor_set(x_92, 1, x_15);
x_93 = l_Int_Linear_Expr_norm(x_92);
lean_dec_ref(x_92);
x_279 = l_Int_Linear_Poly_isUnsatEq(x_93);
if (x_279 == 0)
{
uint8_t x_280; 
x_280 = l_Int_Linear_Poly_isValidEq(x_93);
if (x_280 == 0)
{
lean_object* x_281; uint8_t x_282; 
lean_inc_ref(x_93);
x_281 = l_Int_Linear_Poly_toExpr(x_93);
x_282 = l_Int_Linear_instBEqExpr_beq(x_281, x_13);
lean_dec_ref(x_281);
if (x_282 == 0)
{
x_191 = x_282;
goto block_278;
}
else
{
lean_object* x_283; uint8_t x_284; 
x_283 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35;
x_284 = l_Int_Linear_instBEqExpr_beq(x_15, x_283);
x_191 = x_284;
goto block_278;
}
}
else
{
lean_object* x_285; 
lean_dec_ref(x_93);
lean_dec(x_25);
lean_dec(x_22);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_9);
x_285 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_16, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_285) == 0)
{
uint8_t x_286; 
x_286 = !lean_is_exclusive(x_285);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_287 = lean_ctor_get(x_285, 0);
x_288 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38;
x_289 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41;
x_290 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_13);
x_291 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_292 = l_Lean_eagerReflBoolTrue;
x_293 = l_Lean_mkApp4(x_289, x_287, x_290, x_291, x_292);
x_294 = l_Lean_mkPropEq(x_26, x_288);
x_295 = l_Lean_Meta_mkExpectedPropHint(x_293, x_294);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_288);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_285, 0, x_297);
return x_285;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_298 = lean_ctor_get(x_285, 0);
lean_inc(x_298);
lean_dec(x_285);
x_299 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38;
x_300 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41;
x_301 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_13);
x_302 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_303 = l_Lean_eagerReflBoolTrue;
x_304 = l_Lean_mkApp4(x_300, x_298, x_301, x_302, x_303);
x_305 = l_Lean_mkPropEq(x_26, x_299);
x_306 = l_Lean_Meta_mkExpectedPropHint(x_304, x_305);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_299);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_308, 0, x_307);
x_309 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_309, 0, x_308);
return x_309;
}
}
else
{
uint8_t x_310; 
lean_dec_ref(x_26);
lean_dec(x_15);
lean_dec(x_13);
x_310 = !lean_is_exclusive(x_285);
if (x_310 == 0)
{
return x_285;
}
else
{
lean_object* x_311; lean_object* x_312; 
x_311 = lean_ctor_get(x_285, 0);
lean_inc(x_311);
lean_dec(x_285);
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_311);
return x_312;
}
}
}
}
else
{
lean_object* x_313; 
lean_dec_ref(x_93);
lean_dec(x_25);
lean_dec(x_22);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_9);
x_313 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_16, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_313) == 0)
{
uint8_t x_314; 
x_314 = !lean_is_exclusive(x_313);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_315 = lean_ctor_get(x_313, 0);
x_316 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8;
x_317 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44;
x_318 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_13);
x_319 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_320 = l_Lean_eagerReflBoolTrue;
x_321 = l_Lean_mkApp4(x_317, x_315, x_318, x_319, x_320);
x_322 = l_Lean_mkPropEq(x_26, x_316);
x_323 = l_Lean_Meta_mkExpectedPropHint(x_321, x_322);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_316);
lean_ctor_set(x_324, 1, x_323);
x_325 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_313, 0, x_325);
return x_313;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_326 = lean_ctor_get(x_313, 0);
lean_inc(x_326);
lean_dec(x_313);
x_327 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8;
x_328 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44;
x_329 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_13);
x_330 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_331 = l_Lean_eagerReflBoolTrue;
x_332 = l_Lean_mkApp4(x_328, x_326, x_329, x_330, x_331);
x_333 = l_Lean_mkPropEq(x_26, x_327);
x_334 = l_Lean_Meta_mkExpectedPropHint(x_332, x_333);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_327);
lean_ctor_set(x_335, 1, x_334);
x_336 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_336, 0, x_335);
x_337 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_337, 0, x_336);
return x_337;
}
}
else
{
uint8_t x_338; 
lean_dec_ref(x_26);
lean_dec(x_15);
lean_dec(x_13);
x_338 = !lean_is_exclusive(x_313);
if (x_338 == 0)
{
return x_313;
}
else
{
lean_object* x_339; lean_object* x_340; 
x_339 = lean_ctor_get(x_313, 0);
lean_inc(x_339);
lean_dec(x_313);
x_340 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_340, 0, x_339);
return x_340;
}
}
}
block_41:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = l_Lean_eagerReflBoolTrue;
x_35 = l_Lean_mkApp5(x_29, x_27, x_30, x_31, x_33, x_34);
lean_inc_ref(x_32);
x_36 = l_Lean_mkPropEq(x_26, x_32);
x_37 = l_Lean_Meta_mkExpectedPropHint(x_35, x_36);
if (lean_is_scalar(x_17)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_17;
}
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
if (lean_is_scalar(x_11)) {
 x_39 = lean_alloc_ctor(1, 1, 0);
} else {
 x_39 = x_11;
}
lean_ctor_set(x_39, 0, x_38);
if (lean_is_scalar(x_25)) {
 x_40 = lean_alloc_ctor(0, 1, 0);
} else {
 x_40 = x_25;
}
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
block_57:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = l_Lean_eagerReflBoolTrue;
x_51 = l_Lean_mkApp6(x_47, x_43, x_48, x_45, x_42, x_49, x_50);
lean_inc_ref(x_46);
x_52 = l_Lean_mkPropEq(x_26, x_46);
x_53 = l_Lean_Meta_mkExpectedPropHint(x_51, x_52);
if (lean_is_scalar(x_14)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_14;
}
lean_ctor_set(x_54, 0, x_46);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
if (lean_is_scalar(x_22)) {
 x_56 = lean_alloc_ctor(0, 1, 0);
} else {
 x_56 = x_22;
}
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
block_91:
{
lean_object* x_61; 
x_61 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_16, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc_ref(x_60);
x_64 = l_Lean_mkIntEq(x_59, x_60);
x_65 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4;
x_66 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_13);
x_67 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_68 = l_Lean_mkNatLit(x_58);
x_69 = l_Lean_eagerReflBoolTrue;
x_70 = l_Lean_mkApp6(x_65, x_63, x_66, x_67, x_68, x_60, x_69);
lean_inc_ref(x_64);
x_71 = l_Lean_mkPropEq(x_26, x_64);
x_72 = l_Lean_Meta_mkExpectedPropHint(x_70, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_61, 0, x_74);
return x_61;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_75 = lean_ctor_get(x_61, 0);
lean_inc(x_75);
lean_dec(x_61);
lean_inc_ref(x_60);
x_76 = l_Lean_mkIntEq(x_59, x_60);
x_77 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4;
x_78 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_13);
x_79 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_80 = l_Lean_mkNatLit(x_58);
x_81 = l_Lean_eagerReflBoolTrue;
x_82 = l_Lean_mkApp6(x_77, x_75, x_78, x_79, x_80, x_60, x_81);
lean_inc_ref(x_76);
x_83 = l_Lean_mkPropEq(x_26, x_76);
x_84 = l_Lean_Meta_mkExpectedPropHint(x_82, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_76);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_26);
lean_dec(x_15);
lean_dec(x_13);
x_88 = !lean_is_exclusive(x_61);
if (x_88 == 0)
{
return x_61;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_61, 0);
lean_inc(x_89);
lean_dec(x_61);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
block_190:
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = l_Int_Linear_Poly_gcdCoeffs_x27(x_93);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_dec_eq(x_99, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_102 = l_Int_Linear_Poly_getConst(x_93);
x_103 = lean_nat_to_int(x_99);
x_104 = lean_int_emod(x_102, x_103);
lean_dec(x_102);
x_105 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5;
x_106 = lean_int_dec_eq(x_104, x_105);
lean_dec(x_104);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec_ref(x_93);
lean_dec(x_22);
lean_dec_ref(x_19);
lean_dec(x_14);
x_107 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_16, x_94, x_95, x_96, x_97);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8;
x_110 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11;
x_111 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_13);
x_112 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_113 = lean_int_dec_le(x_105, x_103);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17;
x_115 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
x_116 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22;
x_117 = lean_int_neg(x_103);
lean_dec(x_103);
x_118 = l_Int_toNat(x_117);
lean_dec(x_117);
x_119 = l_Lean_instToExprInt_mkNat(x_118);
x_120 = l_Lean_mkApp3(x_114, x_115, x_116, x_119);
x_27 = x_108;
x_28 = lean_box(0);
x_29 = x_110;
x_30 = x_111;
x_31 = x_112;
x_32 = x_109;
x_33 = x_120;
goto block_41;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = l_Int_toNat(x_103);
lean_dec(x_103);
x_122 = l_Lean_instToExprInt_mkNat(x_121);
x_27 = x_108;
x_28 = lean_box(0);
x_29 = x_110;
x_30 = x_111;
x_31 = x_112;
x_32 = x_109;
x_33 = x_122;
goto block_41;
}
}
else
{
uint8_t x_123; 
lean_dec(x_103);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
x_123 = !lean_is_exclusive(x_107);
if (x_123 == 0)
{
return x_107;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_107, 0);
lean_inc(x_124);
lean_dec(x_107);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_11);
x_126 = l_Int_Linear_Poly_div(x_103, x_93);
lean_inc_ref(x_126);
x_127 = l_Int_Linear_Poly_denoteExpr___redArg(x_19, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec_ref(x_127);
x_129 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_16, x_94, x_95, x_96, x_97);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
x_132 = l_Lean_mkIntEq(x_128, x_131);
x_133 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26;
x_134 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_13);
x_135 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_136 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_126);
x_137 = lean_int_dec_le(x_105, x_103);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_138 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17;
x_139 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
x_140 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22;
x_141 = lean_int_neg(x_103);
lean_dec(x_103);
x_142 = l_Int_toNat(x_141);
lean_dec(x_141);
x_143 = l_Lean_instToExprInt_mkNat(x_142);
x_144 = l_Lean_mkApp3(x_138, x_139, x_140, x_143);
x_42 = x_136;
x_43 = x_130;
x_44 = lean_box(0);
x_45 = x_135;
x_46 = x_132;
x_47 = x_133;
x_48 = x_134;
x_49 = x_144;
goto block_57;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = l_Int_toNat(x_103);
lean_dec(x_103);
x_146 = l_Lean_instToExprInt_mkNat(x_145);
x_42 = x_136;
x_43 = x_130;
x_44 = lean_box(0);
x_45 = x_135;
x_46 = x_132;
x_47 = x_133;
x_48 = x_134;
x_49 = x_146;
goto block_57;
}
}
else
{
uint8_t x_147; 
lean_dec(x_128);
lean_dec_ref(x_126);
lean_dec(x_103);
lean_dec_ref(x_26);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_147 = !lean_is_exclusive(x_129);
if (x_147 == 0)
{
return x_129;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_129, 0);
lean_inc(x_148);
lean_dec(x_129);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
return x_149;
}
}
}
else
{
uint8_t x_150; 
lean_dec_ref(x_126);
lean_dec(x_103);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec_ref(x_26);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_150 = !lean_is_exclusive(x_127);
if (x_150 == 0)
{
return x_127;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_127, 0);
lean_inc(x_151);
lean_dec(x_127);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_151);
return x_152;
}
}
}
}
else
{
lean_object* x_153; 
lean_dec(x_99);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_inc_ref(x_93);
x_153 = l_Int_Linear_Poly_denoteExpr___redArg(x_19, x_93);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec_ref(x_153);
x_155 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_16, x_94, x_95, x_96, x_97);
if (lean_obj_tag(x_155) == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
x_159 = l_Lean_mkIntEq(x_154, x_158);
x_160 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29;
x_161 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_13);
x_162 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_163 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_93);
x_164 = l_Lean_eagerReflBoolTrue;
x_165 = l_Lean_mkApp5(x_160, x_157, x_161, x_162, x_163, x_164);
lean_inc_ref(x_159);
x_166 = l_Lean_mkPropEq(x_26, x_159);
x_167 = l_Lean_Meta_mkExpectedPropHint(x_165, x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_159);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_155, 0, x_169);
return x_155;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_170 = lean_ctor_get(x_155, 0);
lean_inc(x_170);
lean_dec(x_155);
x_171 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
x_172 = l_Lean_mkIntEq(x_154, x_171);
x_173 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29;
x_174 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_13);
x_175 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_176 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_93);
x_177 = l_Lean_eagerReflBoolTrue;
x_178 = l_Lean_mkApp5(x_173, x_170, x_174, x_175, x_176, x_177);
lean_inc_ref(x_172);
x_179 = l_Lean_mkPropEq(x_26, x_172);
x_180 = l_Lean_Meta_mkExpectedPropHint(x_178, x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_172);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_181);
x_183 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_183, 0, x_182);
return x_183;
}
}
else
{
uint8_t x_184; 
lean_dec(x_154);
lean_dec_ref(x_93);
lean_dec_ref(x_26);
lean_dec(x_15);
lean_dec(x_13);
x_184 = !lean_is_exclusive(x_155);
if (x_184 == 0)
{
return x_155;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_155, 0);
lean_inc(x_185);
lean_dec(x_155);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_185);
return x_186;
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec_ref(x_26);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
x_187 = !lean_is_exclusive(x_153);
if (x_187 == 0)
{
return x_153;
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_153, 0);
lean_inc(x_188);
lean_dec(x_153);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
return x_189;
}
}
}
}
block_278:
{
if (x_191 == 0)
{
lean_dec(x_9);
if (lean_obj_tag(x_93) == 1)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_192 = lean_ctor_get(x_93, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_93, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_93, 2);
lean_inc_ref(x_194);
x_195 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30;
x_196 = lean_int_dec_eq(x_192, x_195);
lean_dec(x_192);
if (x_196 == 0)
{
lean_dec_ref(x_194);
lean_dec(x_193);
x_94 = x_2;
x_95 = x_3;
x_96 = x_4;
x_97 = x_5;
x_98 = lean_box(0);
goto block_190;
}
else
{
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
lean_dec_ref(x_93);
lean_dec(x_25);
lean_dec(x_22);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
x_197 = lean_ctor_get(x_194, 0);
lean_inc(x_197);
lean_dec_ref(x_194);
x_198 = lean_array_get_borrowed(x_18, x_16, x_193);
x_199 = lean_int_neg(x_197);
lean_dec(x_197);
x_200 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5;
x_201 = lean_int_dec_le(x_200, x_199);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_202 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17;
x_203 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
x_204 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22;
x_205 = lean_int_neg(x_199);
lean_dec(x_199);
x_206 = l_Int_toNat(x_205);
lean_dec(x_205);
x_207 = l_Lean_instToExprInt_mkNat(x_206);
x_208 = l_Lean_mkApp3(x_202, x_203, x_204, x_207);
lean_inc(x_198);
x_58 = x_193;
x_59 = x_198;
x_60 = x_208;
goto block_91;
}
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = l_Int_toNat(x_199);
lean_dec(x_199);
x_210 = l_Lean_instToExprInt_mkNat(x_209);
lean_inc(x_198);
x_58 = x_193;
x_59 = x_198;
x_60 = x_210;
goto block_91;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_211 = lean_ctor_get(x_194, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_194, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_194, 2);
lean_inc_ref(x_213);
lean_dec_ref(x_194);
x_214 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31;
x_215 = lean_int_dec_eq(x_211, x_214);
lean_dec(x_211);
if (x_215 == 0)
{
lean_dec_ref(x_213);
lean_dec(x_212);
lean_dec(x_193);
x_94 = x_2;
x_95 = x_3;
x_96 = x_4;
x_97 = x_5;
x_98 = lean_box(0);
goto block_190;
}
else
{
if (lean_obj_tag(x_213) == 0)
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_213);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_217 = lean_ctor_get(x_213, 0);
x_218 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5;
x_219 = lean_int_dec_eq(x_217, x_218);
lean_dec(x_217);
if (x_219 == 0)
{
lean_free_object(x_213);
lean_dec(x_212);
lean_dec(x_193);
x_94 = x_2;
x_95 = x_3;
x_96 = x_4;
x_97 = x_5;
x_98 = lean_box(0);
goto block_190;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec_ref(x_93);
lean_dec(x_25);
lean_dec(x_22);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
x_220 = lean_array_get(x_18, x_16, x_193);
x_221 = lean_array_get(x_18, x_16, x_212);
x_222 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_16, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_222) == 0)
{
uint8_t x_223; 
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_224 = lean_ctor_get(x_222, 0);
x_225 = l_Lean_mkIntEq(x_220, x_221);
x_226 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34;
x_227 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_13);
x_228 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_229 = l_Lean_mkNatLit(x_193);
x_230 = l_Lean_mkNatLit(x_212);
x_231 = l_Lean_eagerReflBoolTrue;
x_232 = l_Lean_mkApp6(x_226, x_224, x_227, x_228, x_229, x_230, x_231);
lean_inc_ref(x_225);
x_233 = l_Lean_mkPropEq(x_26, x_225);
x_234 = l_Lean_Meta_mkExpectedPropHint(x_232, x_233);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_225);
lean_ctor_set(x_235, 1, x_234);
lean_ctor_set_tag(x_213, 1);
lean_ctor_set(x_213, 0, x_235);
lean_ctor_set(x_222, 0, x_213);
return x_222;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_236 = lean_ctor_get(x_222, 0);
lean_inc(x_236);
lean_dec(x_222);
x_237 = l_Lean_mkIntEq(x_220, x_221);
x_238 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34;
x_239 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_13);
x_240 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_241 = l_Lean_mkNatLit(x_193);
x_242 = l_Lean_mkNatLit(x_212);
x_243 = l_Lean_eagerReflBoolTrue;
x_244 = l_Lean_mkApp6(x_238, x_236, x_239, x_240, x_241, x_242, x_243);
lean_inc_ref(x_237);
x_245 = l_Lean_mkPropEq(x_26, x_237);
x_246 = l_Lean_Meta_mkExpectedPropHint(x_244, x_245);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_237);
lean_ctor_set(x_247, 1, x_246);
lean_ctor_set_tag(x_213, 1);
lean_ctor_set(x_213, 0, x_247);
x_248 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_248, 0, x_213);
return x_248;
}
}
else
{
uint8_t x_249; 
lean_dec(x_221);
lean_dec(x_220);
lean_free_object(x_213);
lean_dec(x_212);
lean_dec(x_193);
lean_dec_ref(x_26);
lean_dec(x_15);
lean_dec(x_13);
x_249 = !lean_is_exclusive(x_222);
if (x_249 == 0)
{
return x_222;
}
else
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_ctor_get(x_222, 0);
lean_inc(x_250);
lean_dec(x_222);
x_251 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_251, 0, x_250);
return x_251;
}
}
}
}
else
{
lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_252 = lean_ctor_get(x_213, 0);
lean_inc(x_252);
lean_dec(x_213);
x_253 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5;
x_254 = lean_int_dec_eq(x_252, x_253);
lean_dec(x_252);
if (x_254 == 0)
{
lean_dec(x_212);
lean_dec(x_193);
x_94 = x_2;
x_95 = x_3;
x_96 = x_4;
x_97 = x_5;
x_98 = lean_box(0);
goto block_190;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec_ref(x_93);
lean_dec(x_25);
lean_dec(x_22);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
x_255 = lean_array_get(x_18, x_16, x_193);
x_256 = lean_array_get(x_18, x_16, x_212);
x_257 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_16, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_259 = x_257;
} else {
 lean_dec_ref(x_257);
 x_259 = lean_box(0);
}
x_260 = l_Lean_mkIntEq(x_255, x_256);
x_261 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34;
x_262 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_13);
x_263 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_264 = l_Lean_mkNatLit(x_193);
x_265 = l_Lean_mkNatLit(x_212);
x_266 = l_Lean_eagerReflBoolTrue;
x_267 = l_Lean_mkApp6(x_261, x_258, x_262, x_263, x_264, x_265, x_266);
lean_inc_ref(x_260);
x_268 = l_Lean_mkPropEq(x_26, x_260);
x_269 = l_Lean_Meta_mkExpectedPropHint(x_267, x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_260);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_270);
if (lean_is_scalar(x_259)) {
 x_272 = lean_alloc_ctor(0, 1, 0);
} else {
 x_272 = x_259;
}
lean_ctor_set(x_272, 0, x_271);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_212);
lean_dec(x_193);
lean_dec_ref(x_26);
lean_dec(x_15);
lean_dec(x_13);
x_273 = lean_ctor_get(x_257, 0);
lean_inc(x_273);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 x_274 = x_257;
} else {
 lean_dec_ref(x_257);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 1, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_273);
return x_275;
}
}
}
}
else
{
lean_dec_ref(x_213);
lean_dec(x_212);
lean_dec(x_193);
x_94 = x_2;
x_95 = x_3;
x_96 = x_4;
x_97 = x_5;
x_98 = lean_box(0);
goto block_190;
}
}
}
}
}
else
{
x_94 = x_2;
x_95 = x_3;
x_96 = x_4;
x_97 = x_5;
x_98 = lean_box(0);
goto block_190;
}
}
else
{
lean_object* x_276; lean_object* x_277; 
lean_dec_ref(x_93);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_22);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_276 = lean_box(0);
if (lean_is_scalar(x_9)) {
 x_277 = lean_alloc_ctor(0, 1, 0);
} else {
 x_277 = x_9;
}
lean_ctor_set(x_277, 0, x_276);
return x_277;
}
}
}
else
{
uint8_t x_341; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_341 = !lean_is_exclusive(x_23);
if (x_341 == 0)
{
return x_23;
}
else
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_ctor_get(x_23, 0);
lean_inc(x_342);
lean_dec(x_23);
x_343 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_343, 0, x_342);
return x_343;
}
}
}
else
{
uint8_t x_344; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_344 = !lean_is_exclusive(x_20);
if (x_344 == 0)
{
return x_20;
}
else
{
lean_object* x_345; lean_object* x_346; 
x_345 = lean_ctor_get(x_20, 0);
lean_inc(x_345);
lean_dec(x_20);
x_346 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_346, 0, x_345);
return x_346;
}
}
}
else
{
lean_object* x_347; lean_object* x_348; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_347 = lean_box(0);
if (lean_is_scalar(x_9)) {
 x_348 = lean_alloc_ctor(0, 1, 0);
} else {
 x_348 = x_9;
}
lean_ctor_set(x_348, 0, x_347);
return x_348;
}
}
else
{
uint8_t x_349; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_349 = !lean_is_exclusive(x_7);
if (x_349 == 0)
{
return x_7;
}
else
{
lean_object* x_350; lean_object* x_351; 
x_350 = lean_ctor_get(x_7, 0);
lean_inc(x_350);
lean_dec(x_7);
x_351 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_351, 0, x_350);
return x_351;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_le_coeff", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_le_coeff_tight", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_le", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_eq_true", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_eq_false", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_163; uint8_t x_164; lean_object* x_540; uint8_t x_541; 
x_163 = l_Lean_instInhabitedExpr;
x_540 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17;
x_541 = l_Lean_Expr_isAppOf(x_1, x_540);
if (x_541 == 0)
{
x_164 = x_541;
goto block_539;
}
else
{
x_164 = x_2;
goto block_539;
}
block_17:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc_ref(x_9);
x_12 = l_Lean_mkPropEq(x_8, x_9);
x_13 = l_Lean_Meta_mkExpectedPropHint(x_10, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
block_29:
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_eagerReflBoolTrue;
x_28 = l_Lean_mkApp6(x_23, x_22, x_24, x_20, x_18, x_26, x_27);
x_8 = x_19;
x_9 = x_21;
x_10 = x_28;
x_11 = lean_box(0);
goto block_17;
}
block_41:
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_eagerReflBoolTrue;
x_40 = l_Lean_mkApp6(x_31, x_35, x_37, x_32, x_36, x_38, x_39);
x_8 = x_30;
x_9 = x_33;
x_10 = x_40;
x_11 = lean_box(0);
goto block_17;
}
block_107:
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_Int_Linear_Poly_div(x_49, x_44);
lean_inc_ref(x_53);
x_54 = l_Int_Linear_Poly_denoteExpr___redArg(x_51, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = l_Lean_mkIntLit(x_47);
x_57 = l_Lean_mkIntLE(x_55, x_56);
if (x_52 == 0)
{
lean_object* x_58; 
x_58 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_42, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_box(0);
x_61 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2;
x_62 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_48);
x_63 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_46);
x_64 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_53);
x_65 = lean_int_dec_le(x_47, x_49);
lean_dec(x_47);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_66 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14;
x_67 = l_Lean_Level_ofNat(x_45);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_60);
x_69 = l_Lean_Expr_const___override(x_66, x_68);
x_70 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
x_71 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22;
x_72 = lean_int_neg(x_49);
lean_dec(x_49);
x_73 = l_Int_toNat(x_72);
lean_dec(x_72);
x_74 = l_Lean_instToExprInt_mkNat(x_73);
x_75 = l_Lean_mkApp3(x_69, x_70, x_71, x_74);
x_30 = x_43;
x_31 = x_61;
x_32 = x_63;
x_33 = x_57;
x_34 = lean_box(0);
x_35 = x_59;
x_36 = x_64;
x_37 = x_62;
x_38 = x_75;
goto block_41;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Int_toNat(x_49);
lean_dec(x_49);
x_77 = l_Lean_instToExprInt_mkNat(x_76);
x_30 = x_43;
x_31 = x_61;
x_32 = x_63;
x_33 = x_57;
x_34 = lean_box(0);
x_35 = x_59;
x_36 = x_64;
x_37 = x_62;
x_38 = x_77;
goto block_41;
}
}
else
{
uint8_t x_78; 
lean_dec_ref(x_57);
lean_dec_ref(x_53);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_43);
x_78 = !lean_is_exclusive(x_58);
if (x_78 == 0)
{
return x_58;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_58, 0);
lean_inc(x_79);
lean_dec(x_58);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; 
x_81 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_42, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = lean_box(0);
x_84 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5;
x_85 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_48);
x_86 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_46);
x_87 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_53);
x_88 = lean_int_dec_le(x_47, x_49);
lean_dec(x_47);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_89 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14;
x_90 = l_Lean_Level_ofNat(x_45);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_83);
x_92 = l_Lean_Expr_const___override(x_89, x_91);
x_93 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
x_94 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22;
x_95 = lean_int_neg(x_49);
lean_dec(x_49);
x_96 = l_Int_toNat(x_95);
lean_dec(x_95);
x_97 = l_Lean_instToExprInt_mkNat(x_96);
x_98 = l_Lean_mkApp3(x_92, x_93, x_94, x_97);
x_18 = x_87;
x_19 = x_43;
x_20 = x_86;
x_21 = x_57;
x_22 = x_82;
x_23 = x_84;
x_24 = x_85;
x_25 = lean_box(0);
x_26 = x_98;
goto block_29;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Int_toNat(x_49);
lean_dec(x_49);
x_100 = l_Lean_instToExprInt_mkNat(x_99);
x_18 = x_87;
x_19 = x_43;
x_20 = x_86;
x_21 = x_57;
x_22 = x_82;
x_23 = x_84;
x_24 = x_85;
x_25 = lean_box(0);
x_26 = x_100;
goto block_29;
}
}
else
{
uint8_t x_101; 
lean_dec_ref(x_57);
lean_dec_ref(x_53);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_43);
x_101 = !lean_is_exclusive(x_81);
if (x_101 == 0)
{
return x_81;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_81, 0);
lean_inc(x_102);
lean_dec(x_81);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec_ref(x_53);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_43);
lean_dec_ref(x_42);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_104 = !lean_is_exclusive(x_54);
if (x_104 == 0)
{
return x_54;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_54, 0);
lean_inc(x_105);
lean_dec(x_54);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
block_162:
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = l_Int_Linear_Poly_gcdCoeffs_x27(x_110);
x_116 = lean_unsigned_to_nat(1u);
x_117 = lean_nat_dec_eq(x_115, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_118 = l_Int_Linear_Poly_getConst(x_110);
x_119 = lean_nat_to_int(x_115);
x_120 = lean_int_emod(x_118, x_119);
lean_dec(x_118);
x_121 = lean_unsigned_to_nat(0u);
x_122 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5;
x_123 = lean_int_dec_eq(x_120, x_122);
lean_dec(x_120);
if (x_123 == 0)
{
uint8_t x_124; 
x_124 = 1;
x_42 = x_109;
x_43 = x_108;
x_44 = x_110;
x_45 = x_121;
x_46 = x_111;
x_47 = x_122;
x_48 = x_112;
x_49 = x_119;
x_50 = lean_box(0);
x_51 = x_113;
x_52 = x_124;
goto block_107;
}
else
{
x_42 = x_109;
x_43 = x_108;
x_44 = x_110;
x_45 = x_121;
x_46 = x_111;
x_47 = x_122;
x_48 = x_112;
x_49 = x_119;
x_50 = lean_box(0);
x_51 = x_113;
x_52 = x_117;
goto block_107;
}
}
else
{
lean_object* x_125; 
lean_dec(x_115);
lean_inc_ref(x_110);
x_125 = l_Int_Linear_Poly_denoteExpr___redArg(x_113, x_110);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_109, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
x_131 = l_Lean_mkIntLE(x_126, x_130);
x_132 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8;
x_133 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_112);
x_134 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_111);
x_135 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_110);
x_136 = l_Lean_eagerReflBoolTrue;
x_137 = l_Lean_mkApp5(x_132, x_129, x_133, x_134, x_135, x_136);
lean_inc_ref(x_131);
x_138 = l_Lean_mkPropEq(x_108, x_131);
x_139 = l_Lean_Meta_mkExpectedPropHint(x_137, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_131);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_127, 0, x_141);
return x_127;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_142 = lean_ctor_get(x_127, 0);
lean_inc(x_142);
lean_dec(x_127);
x_143 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
x_144 = l_Lean_mkIntLE(x_126, x_143);
x_145 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8;
x_146 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_112);
x_147 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_111);
x_148 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_110);
x_149 = l_Lean_eagerReflBoolTrue;
x_150 = l_Lean_mkApp5(x_145, x_142, x_146, x_147, x_148, x_149);
lean_inc_ref(x_144);
x_151 = l_Lean_mkPropEq(x_108, x_144);
x_152 = l_Lean_Meta_mkExpectedPropHint(x_150, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_144);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
}
else
{
uint8_t x_156; 
lean_dec(x_126);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_108);
x_156 = !lean_is_exclusive(x_127);
if (x_156 == 0)
{
return x_127;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_127, 0);
lean_inc(x_157);
lean_dec(x_127);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
}
}
else
{
uint8_t x_159; 
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_108);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_159 = !lean_is_exclusive(x_125);
if (x_159 == 0)
{
return x_125;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_125, 0);
lean_inc(x_160);
lean_dec(x_125);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
}
}
}
block_539:
{
lean_object* x_165; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_165 = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_165) == 0)
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_165, 0);
if (lean_obj_tag(x_167) == 1)
{
uint8_t x_168; 
lean_free_object(x_165);
x_168 = !lean_is_exclusive(x_167);
if (x_168 == 0)
{
lean_object* x_169; uint8_t x_170; 
x_169 = lean_ctor_get(x_167, 0);
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; uint8_t x_172; 
x_171 = lean_ctor_get(x_169, 1);
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_173 = lean_ctor_get(x_169, 0);
x_174 = lean_ctor_get(x_171, 0);
x_175 = lean_ctor_get(x_171, 1);
lean_inc(x_175);
x_176 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_176, 0, x_163);
lean_closure_set(x_176, 1, x_175);
lean_inc(x_173);
lean_inc_ref(x_176);
x_177 = l_Int_Linear_Expr_denoteExpr___redArg(x_176, x_173);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec_ref(x_177);
lean_inc(x_174);
lean_inc_ref(x_176);
x_179 = l_Int_Linear_Expr_denoteExpr___redArg(x_176, x_174);
if (lean_obj_tag(x_179) == 0)
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_181 = lean_ctor_get(x_179, 0);
x_182 = l_Lean_mkIntLE(x_178, x_181);
lean_inc(x_174);
lean_inc(x_173);
lean_ctor_set_tag(x_169, 3);
lean_ctor_set(x_169, 1, x_174);
x_183 = l_Int_Linear_Expr_norm(x_169);
lean_dec_ref(x_169);
x_184 = l_Int_Linear_Poly_isUnsatLe(x_183);
if (x_184 == 0)
{
uint8_t x_185; 
x_185 = l_Int_Linear_Poly_isValidLe(x_183);
if (x_185 == 0)
{
lean_free_object(x_171);
lean_free_object(x_167);
if (x_164 == 0)
{
lean_free_object(x_179);
x_108 = x_182;
x_109 = x_175;
x_110 = x_183;
x_111 = x_174;
x_112 = x_173;
x_113 = x_176;
x_114 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_186; uint8_t x_187; 
lean_inc_ref(x_183);
x_186 = l_Int_Linear_Poly_toExpr(x_183);
x_187 = l_Int_Linear_instBEqExpr_beq(x_186, x_173);
lean_dec_ref(x_186);
if (x_187 == 0)
{
lean_free_object(x_179);
x_108 = x_182;
x_109 = x_175;
x_110 = x_183;
x_111 = x_174;
x_112 = x_173;
x_113 = x_176;
x_114 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_188; uint8_t x_189; 
x_188 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35;
x_189 = l_Int_Linear_instBEqExpr_beq(x_174, x_188);
if (x_189 == 0)
{
lean_free_object(x_179);
x_108 = x_182;
x_109 = x_175;
x_110 = x_183;
x_111 = x_174;
x_112 = x_173;
x_113 = x_176;
x_114 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_190; 
lean_dec_ref(x_183);
lean_dec_ref(x_182);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_190 = lean_box(0);
lean_ctor_set(x_179, 0, x_190);
return x_179;
}
}
}
}
else
{
lean_object* x_191; 
lean_dec_ref(x_183);
lean_free_object(x_179);
lean_dec_ref(x_176);
x_191 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_175, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_191) == 0)
{
uint8_t x_192; 
x_192 = !lean_is_exclusive(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_193 = lean_ctor_get(x_191, 0);
x_194 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38;
x_195 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
x_196 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_173);
x_197 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_174);
x_198 = l_Lean_eagerReflBoolTrue;
x_199 = l_Lean_mkApp4(x_195, x_193, x_196, x_197, x_198);
x_200 = l_Lean_mkPropEq(x_182, x_194);
x_201 = l_Lean_Meta_mkExpectedPropHint(x_199, x_200);
lean_ctor_set(x_171, 1, x_201);
lean_ctor_set(x_171, 0, x_194);
lean_ctor_set(x_167, 0, x_171);
lean_ctor_set(x_191, 0, x_167);
return x_191;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_202 = lean_ctor_get(x_191, 0);
lean_inc(x_202);
lean_dec(x_191);
x_203 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38;
x_204 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
x_205 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_173);
x_206 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_174);
x_207 = l_Lean_eagerReflBoolTrue;
x_208 = l_Lean_mkApp4(x_204, x_202, x_205, x_206, x_207);
x_209 = l_Lean_mkPropEq(x_182, x_203);
x_210 = l_Lean_Meta_mkExpectedPropHint(x_208, x_209);
lean_ctor_set(x_171, 1, x_210);
lean_ctor_set(x_171, 0, x_203);
lean_ctor_set(x_167, 0, x_171);
x_211 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_211, 0, x_167);
return x_211;
}
}
else
{
uint8_t x_212; 
lean_dec_ref(x_182);
lean_free_object(x_171);
lean_dec(x_174);
lean_dec(x_173);
lean_free_object(x_167);
x_212 = !lean_is_exclusive(x_191);
if (x_212 == 0)
{
return x_191;
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_191, 0);
lean_inc(x_213);
lean_dec(x_191);
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_213);
return x_214;
}
}
}
}
else
{
lean_object* x_215; 
lean_dec_ref(x_183);
lean_free_object(x_179);
lean_dec_ref(x_176);
x_215 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_175, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_215) == 0)
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_217 = lean_ctor_get(x_215, 0);
x_218 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8;
x_219 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
x_220 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_173);
x_221 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_174);
x_222 = l_Lean_eagerReflBoolTrue;
x_223 = l_Lean_mkApp4(x_219, x_217, x_220, x_221, x_222);
x_224 = l_Lean_mkPropEq(x_182, x_218);
x_225 = l_Lean_Meta_mkExpectedPropHint(x_223, x_224);
lean_ctor_set(x_171, 1, x_225);
lean_ctor_set(x_171, 0, x_218);
lean_ctor_set(x_167, 0, x_171);
lean_ctor_set(x_215, 0, x_167);
return x_215;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_226 = lean_ctor_get(x_215, 0);
lean_inc(x_226);
lean_dec(x_215);
x_227 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8;
x_228 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
x_229 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_173);
x_230 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_174);
x_231 = l_Lean_eagerReflBoolTrue;
x_232 = l_Lean_mkApp4(x_228, x_226, x_229, x_230, x_231);
x_233 = l_Lean_mkPropEq(x_182, x_227);
x_234 = l_Lean_Meta_mkExpectedPropHint(x_232, x_233);
lean_ctor_set(x_171, 1, x_234);
lean_ctor_set(x_171, 0, x_227);
lean_ctor_set(x_167, 0, x_171);
x_235 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_235, 0, x_167);
return x_235;
}
}
else
{
uint8_t x_236; 
lean_dec_ref(x_182);
lean_free_object(x_171);
lean_dec(x_174);
lean_dec(x_173);
lean_free_object(x_167);
x_236 = !lean_is_exclusive(x_215);
if (x_236 == 0)
{
return x_215;
}
else
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_215, 0);
lean_inc(x_237);
lean_dec(x_215);
x_238 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_238, 0, x_237);
return x_238;
}
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_239 = lean_ctor_get(x_179, 0);
lean_inc(x_239);
lean_dec(x_179);
x_240 = l_Lean_mkIntLE(x_178, x_239);
lean_inc(x_174);
lean_inc(x_173);
lean_ctor_set_tag(x_169, 3);
lean_ctor_set(x_169, 1, x_174);
x_241 = l_Int_Linear_Expr_norm(x_169);
lean_dec_ref(x_169);
x_242 = l_Int_Linear_Poly_isUnsatLe(x_241);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = l_Int_Linear_Poly_isValidLe(x_241);
if (x_243 == 0)
{
lean_free_object(x_171);
lean_free_object(x_167);
if (x_164 == 0)
{
x_108 = x_240;
x_109 = x_175;
x_110 = x_241;
x_111 = x_174;
x_112 = x_173;
x_113 = x_176;
x_114 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_244; uint8_t x_245; 
lean_inc_ref(x_241);
x_244 = l_Int_Linear_Poly_toExpr(x_241);
x_245 = l_Int_Linear_instBEqExpr_beq(x_244, x_173);
lean_dec_ref(x_244);
if (x_245 == 0)
{
x_108 = x_240;
x_109 = x_175;
x_110 = x_241;
x_111 = x_174;
x_112 = x_173;
x_113 = x_176;
x_114 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_246; uint8_t x_247; 
x_246 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35;
x_247 = l_Int_Linear_instBEqExpr_beq(x_174, x_246);
if (x_247 == 0)
{
x_108 = x_240;
x_109 = x_175;
x_110 = x_241;
x_111 = x_174;
x_112 = x_173;
x_113 = x_176;
x_114 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_248; lean_object* x_249; 
lean_dec_ref(x_241);
lean_dec_ref(x_240);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_248 = lean_box(0);
x_249 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_249, 0, x_248);
return x_249;
}
}
}
}
else
{
lean_object* x_250; 
lean_dec_ref(x_241);
lean_dec_ref(x_176);
x_250 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_175, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_252 = x_250;
} else {
 lean_dec_ref(x_250);
 x_252 = lean_box(0);
}
x_253 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38;
x_254 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
x_255 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_173);
x_256 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_174);
x_257 = l_Lean_eagerReflBoolTrue;
x_258 = l_Lean_mkApp4(x_254, x_251, x_255, x_256, x_257);
x_259 = l_Lean_mkPropEq(x_240, x_253);
x_260 = l_Lean_Meta_mkExpectedPropHint(x_258, x_259);
lean_ctor_set(x_171, 1, x_260);
lean_ctor_set(x_171, 0, x_253);
lean_ctor_set(x_167, 0, x_171);
if (lean_is_scalar(x_252)) {
 x_261 = lean_alloc_ctor(0, 1, 0);
} else {
 x_261 = x_252;
}
lean_ctor_set(x_261, 0, x_167);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec_ref(x_240);
lean_free_object(x_171);
lean_dec(x_174);
lean_dec(x_173);
lean_free_object(x_167);
x_262 = lean_ctor_get(x_250, 0);
lean_inc(x_262);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_263 = x_250;
} else {
 lean_dec_ref(x_250);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(1, 1, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_262);
return x_264;
}
}
}
else
{
lean_object* x_265; 
lean_dec_ref(x_241);
lean_dec_ref(x_176);
x_265 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_175, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 x_267 = x_265;
} else {
 lean_dec_ref(x_265);
 x_267 = lean_box(0);
}
x_268 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8;
x_269 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
x_270 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_173);
x_271 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_174);
x_272 = l_Lean_eagerReflBoolTrue;
x_273 = l_Lean_mkApp4(x_269, x_266, x_270, x_271, x_272);
x_274 = l_Lean_mkPropEq(x_240, x_268);
x_275 = l_Lean_Meta_mkExpectedPropHint(x_273, x_274);
lean_ctor_set(x_171, 1, x_275);
lean_ctor_set(x_171, 0, x_268);
lean_ctor_set(x_167, 0, x_171);
if (lean_is_scalar(x_267)) {
 x_276 = lean_alloc_ctor(0, 1, 0);
} else {
 x_276 = x_267;
}
lean_ctor_set(x_276, 0, x_167);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec_ref(x_240);
lean_free_object(x_171);
lean_dec(x_174);
lean_dec(x_173);
lean_free_object(x_167);
x_277 = lean_ctor_get(x_265, 0);
lean_inc(x_277);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 x_278 = x_265;
} else {
 lean_dec_ref(x_265);
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
}
else
{
uint8_t x_280; 
lean_dec(x_178);
lean_dec_ref(x_176);
lean_free_object(x_171);
lean_dec(x_175);
lean_dec(x_174);
lean_free_object(x_169);
lean_dec(x_173);
lean_free_object(x_167);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_280 = !lean_is_exclusive(x_179);
if (x_280 == 0)
{
return x_179;
}
else
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_179, 0);
lean_inc(x_281);
lean_dec(x_179);
x_282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_282, 0, x_281);
return x_282;
}
}
}
else
{
uint8_t x_283; 
lean_dec_ref(x_176);
lean_free_object(x_171);
lean_dec(x_175);
lean_dec(x_174);
lean_free_object(x_169);
lean_dec(x_173);
lean_free_object(x_167);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_283 = !lean_is_exclusive(x_177);
if (x_283 == 0)
{
return x_177;
}
else
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_177, 0);
lean_inc(x_284);
lean_dec(x_177);
x_285 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_285, 0, x_284);
return x_285;
}
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_286 = lean_ctor_get(x_169, 0);
x_287 = lean_ctor_get(x_171, 0);
x_288 = lean_ctor_get(x_171, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_171);
lean_inc(x_288);
x_289 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_289, 0, x_163);
lean_closure_set(x_289, 1, x_288);
lean_inc(x_286);
lean_inc_ref(x_289);
x_290 = l_Int_Linear_Expr_denoteExpr___redArg(x_289, x_286);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
lean_dec_ref(x_290);
lean_inc(x_287);
lean_inc_ref(x_289);
x_292 = l_Int_Linear_Expr_denoteExpr___redArg(x_289, x_287);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 x_294 = x_292;
} else {
 lean_dec_ref(x_292);
 x_294 = lean_box(0);
}
x_295 = l_Lean_mkIntLE(x_291, x_293);
lean_inc(x_287);
lean_inc(x_286);
lean_ctor_set_tag(x_169, 3);
lean_ctor_set(x_169, 1, x_287);
x_296 = l_Int_Linear_Expr_norm(x_169);
lean_dec_ref(x_169);
x_297 = l_Int_Linear_Poly_isUnsatLe(x_296);
if (x_297 == 0)
{
uint8_t x_298; 
x_298 = l_Int_Linear_Poly_isValidLe(x_296);
if (x_298 == 0)
{
lean_free_object(x_167);
if (x_164 == 0)
{
lean_dec(x_294);
x_108 = x_295;
x_109 = x_288;
x_110 = x_296;
x_111 = x_287;
x_112 = x_286;
x_113 = x_289;
x_114 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_299; uint8_t x_300; 
lean_inc_ref(x_296);
x_299 = l_Int_Linear_Poly_toExpr(x_296);
x_300 = l_Int_Linear_instBEqExpr_beq(x_299, x_286);
lean_dec_ref(x_299);
if (x_300 == 0)
{
lean_dec(x_294);
x_108 = x_295;
x_109 = x_288;
x_110 = x_296;
x_111 = x_287;
x_112 = x_286;
x_113 = x_289;
x_114 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_301; uint8_t x_302; 
x_301 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35;
x_302 = l_Int_Linear_instBEqExpr_beq(x_287, x_301);
if (x_302 == 0)
{
lean_dec(x_294);
x_108 = x_295;
x_109 = x_288;
x_110 = x_296;
x_111 = x_287;
x_112 = x_286;
x_113 = x_289;
x_114 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_303; lean_object* x_304; 
lean_dec_ref(x_296);
lean_dec_ref(x_295);
lean_dec_ref(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_303 = lean_box(0);
if (lean_is_scalar(x_294)) {
 x_304 = lean_alloc_ctor(0, 1, 0);
} else {
 x_304 = x_294;
}
lean_ctor_set(x_304, 0, x_303);
return x_304;
}
}
}
}
else
{
lean_object* x_305; 
lean_dec_ref(x_296);
lean_dec(x_294);
lean_dec_ref(x_289);
x_305 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_288, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 x_307 = x_305;
} else {
 lean_dec_ref(x_305);
 x_307 = lean_box(0);
}
x_308 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38;
x_309 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
x_310 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_286);
x_311 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_287);
x_312 = l_Lean_eagerReflBoolTrue;
x_313 = l_Lean_mkApp4(x_309, x_306, x_310, x_311, x_312);
x_314 = l_Lean_mkPropEq(x_295, x_308);
x_315 = l_Lean_Meta_mkExpectedPropHint(x_313, x_314);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_308);
lean_ctor_set(x_316, 1, x_315);
lean_ctor_set(x_167, 0, x_316);
if (lean_is_scalar(x_307)) {
 x_317 = lean_alloc_ctor(0, 1, 0);
} else {
 x_317 = x_307;
}
lean_ctor_set(x_317, 0, x_167);
return x_317;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec_ref(x_295);
lean_dec(x_287);
lean_dec(x_286);
lean_free_object(x_167);
x_318 = lean_ctor_get(x_305, 0);
lean_inc(x_318);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 x_319 = x_305;
} else {
 lean_dec_ref(x_305);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 1, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_318);
return x_320;
}
}
}
else
{
lean_object* x_321; 
lean_dec_ref(x_296);
lean_dec(x_294);
lean_dec_ref(x_289);
x_321 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_288, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 x_323 = x_321;
} else {
 lean_dec_ref(x_321);
 x_323 = lean_box(0);
}
x_324 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8;
x_325 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
x_326 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_286);
x_327 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_287);
x_328 = l_Lean_eagerReflBoolTrue;
x_329 = l_Lean_mkApp4(x_325, x_322, x_326, x_327, x_328);
x_330 = l_Lean_mkPropEq(x_295, x_324);
x_331 = l_Lean_Meta_mkExpectedPropHint(x_329, x_330);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_324);
lean_ctor_set(x_332, 1, x_331);
lean_ctor_set(x_167, 0, x_332);
if (lean_is_scalar(x_323)) {
 x_333 = lean_alloc_ctor(0, 1, 0);
} else {
 x_333 = x_323;
}
lean_ctor_set(x_333, 0, x_167);
return x_333;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec_ref(x_295);
lean_dec(x_287);
lean_dec(x_286);
lean_free_object(x_167);
x_334 = lean_ctor_get(x_321, 0);
lean_inc(x_334);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 x_335 = x_321;
} else {
 lean_dec_ref(x_321);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(1, 1, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_334);
return x_336;
}
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_291);
lean_dec_ref(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_free_object(x_169);
lean_dec(x_286);
lean_free_object(x_167);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_337 = lean_ctor_get(x_292, 0);
lean_inc(x_337);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 x_338 = x_292;
} else {
 lean_dec_ref(x_292);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(1, 1, 0);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_337);
return x_339;
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec_ref(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_free_object(x_169);
lean_dec(x_286);
lean_free_object(x_167);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_340 = lean_ctor_get(x_290, 0);
lean_inc(x_340);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 x_341 = x_290;
} else {
 lean_dec_ref(x_290);
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
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_343 = lean_ctor_get(x_169, 1);
x_344 = lean_ctor_get(x_169, 0);
lean_inc(x_343);
lean_inc(x_344);
lean_dec(x_169);
x_345 = lean_ctor_get(x_343, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_343, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_347 = x_343;
} else {
 lean_dec_ref(x_343);
 x_347 = lean_box(0);
}
lean_inc(x_346);
x_348 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_348, 0, x_163);
lean_closure_set(x_348, 1, x_346);
lean_inc(x_344);
lean_inc_ref(x_348);
x_349 = l_Int_Linear_Expr_denoteExpr___redArg(x_348, x_344);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
lean_dec_ref(x_349);
lean_inc(x_345);
lean_inc_ref(x_348);
x_351 = l_Int_Linear_Expr_denoteExpr___redArg(x_348, x_345);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 x_353 = x_351;
} else {
 lean_dec_ref(x_351);
 x_353 = lean_box(0);
}
x_354 = l_Lean_mkIntLE(x_350, x_352);
lean_inc(x_345);
lean_inc(x_344);
x_355 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_355, 0, x_344);
lean_ctor_set(x_355, 1, x_345);
x_356 = l_Int_Linear_Expr_norm(x_355);
lean_dec_ref(x_355);
x_357 = l_Int_Linear_Poly_isUnsatLe(x_356);
if (x_357 == 0)
{
uint8_t x_358; 
x_358 = l_Int_Linear_Poly_isValidLe(x_356);
if (x_358 == 0)
{
lean_dec(x_347);
lean_free_object(x_167);
if (x_164 == 0)
{
lean_dec(x_353);
x_108 = x_354;
x_109 = x_346;
x_110 = x_356;
x_111 = x_345;
x_112 = x_344;
x_113 = x_348;
x_114 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_359; uint8_t x_360; 
lean_inc_ref(x_356);
x_359 = l_Int_Linear_Poly_toExpr(x_356);
x_360 = l_Int_Linear_instBEqExpr_beq(x_359, x_344);
lean_dec_ref(x_359);
if (x_360 == 0)
{
lean_dec(x_353);
x_108 = x_354;
x_109 = x_346;
x_110 = x_356;
x_111 = x_345;
x_112 = x_344;
x_113 = x_348;
x_114 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_361; uint8_t x_362; 
x_361 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35;
x_362 = l_Int_Linear_instBEqExpr_beq(x_345, x_361);
if (x_362 == 0)
{
lean_dec(x_353);
x_108 = x_354;
x_109 = x_346;
x_110 = x_356;
x_111 = x_345;
x_112 = x_344;
x_113 = x_348;
x_114 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_363; lean_object* x_364; 
lean_dec_ref(x_356);
lean_dec_ref(x_354);
lean_dec_ref(x_348);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_363 = lean_box(0);
if (lean_is_scalar(x_353)) {
 x_364 = lean_alloc_ctor(0, 1, 0);
} else {
 x_364 = x_353;
}
lean_ctor_set(x_364, 0, x_363);
return x_364;
}
}
}
}
else
{
lean_object* x_365; 
lean_dec_ref(x_356);
lean_dec(x_353);
lean_dec_ref(x_348);
x_365 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_346, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 x_367 = x_365;
} else {
 lean_dec_ref(x_365);
 x_367 = lean_box(0);
}
x_368 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38;
x_369 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
x_370 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_344);
x_371 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_345);
x_372 = l_Lean_eagerReflBoolTrue;
x_373 = l_Lean_mkApp4(x_369, x_366, x_370, x_371, x_372);
x_374 = l_Lean_mkPropEq(x_354, x_368);
x_375 = l_Lean_Meta_mkExpectedPropHint(x_373, x_374);
if (lean_is_scalar(x_347)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_347;
}
lean_ctor_set(x_376, 0, x_368);
lean_ctor_set(x_376, 1, x_375);
lean_ctor_set(x_167, 0, x_376);
if (lean_is_scalar(x_367)) {
 x_377 = lean_alloc_ctor(0, 1, 0);
} else {
 x_377 = x_367;
}
lean_ctor_set(x_377, 0, x_167);
return x_377;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec_ref(x_354);
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_344);
lean_free_object(x_167);
x_378 = lean_ctor_get(x_365, 0);
lean_inc(x_378);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 x_379 = x_365;
} else {
 lean_dec_ref(x_365);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(1, 1, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_378);
return x_380;
}
}
}
else
{
lean_object* x_381; 
lean_dec_ref(x_356);
lean_dec(x_353);
lean_dec_ref(x_348);
x_381 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_346, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 x_383 = x_381;
} else {
 lean_dec_ref(x_381);
 x_383 = lean_box(0);
}
x_384 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8;
x_385 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
x_386 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_344);
x_387 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_345);
x_388 = l_Lean_eagerReflBoolTrue;
x_389 = l_Lean_mkApp4(x_385, x_382, x_386, x_387, x_388);
x_390 = l_Lean_mkPropEq(x_354, x_384);
x_391 = l_Lean_Meta_mkExpectedPropHint(x_389, x_390);
if (lean_is_scalar(x_347)) {
 x_392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_392 = x_347;
}
lean_ctor_set(x_392, 0, x_384);
lean_ctor_set(x_392, 1, x_391);
lean_ctor_set(x_167, 0, x_392);
if (lean_is_scalar(x_383)) {
 x_393 = lean_alloc_ctor(0, 1, 0);
} else {
 x_393 = x_383;
}
lean_ctor_set(x_393, 0, x_167);
return x_393;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec_ref(x_354);
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_344);
lean_free_object(x_167);
x_394 = lean_ctor_get(x_381, 0);
lean_inc(x_394);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 x_395 = x_381;
} else {
 lean_dec_ref(x_381);
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
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_350);
lean_dec_ref(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_344);
lean_free_object(x_167);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_397 = lean_ctor_get(x_351, 0);
lean_inc(x_397);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 x_398 = x_351;
} else {
 lean_dec_ref(x_351);
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
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec_ref(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_344);
lean_free_object(x_167);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_400 = lean_ctor_get(x_349, 0);
lean_inc(x_400);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 x_401 = x_349;
} else {
 lean_dec_ref(x_349);
 x_401 = lean_box(0);
}
if (lean_is_scalar(x_401)) {
 x_402 = lean_alloc_ctor(1, 1, 0);
} else {
 x_402 = x_401;
}
lean_ctor_set(x_402, 0, x_400);
return x_402;
}
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_403 = lean_ctor_get(x_167, 0);
lean_inc(x_403);
lean_dec(x_167);
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 0);
lean_inc(x_405);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 x_406 = x_403;
} else {
 lean_dec_ref(x_403);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_404, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_404, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_409 = x_404;
} else {
 lean_dec_ref(x_404);
 x_409 = lean_box(0);
}
lean_inc(x_408);
x_410 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_410, 0, x_163);
lean_closure_set(x_410, 1, x_408);
lean_inc(x_405);
lean_inc_ref(x_410);
x_411 = l_Int_Linear_Expr_denoteExpr___redArg(x_410, x_405);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
lean_dec_ref(x_411);
lean_inc(x_407);
lean_inc_ref(x_410);
x_413 = l_Int_Linear_Expr_denoteExpr___redArg(x_410, x_407);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; 
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 x_415 = x_413;
} else {
 lean_dec_ref(x_413);
 x_415 = lean_box(0);
}
x_416 = l_Lean_mkIntLE(x_412, x_414);
lean_inc(x_407);
lean_inc(x_405);
if (lean_is_scalar(x_406)) {
 x_417 = lean_alloc_ctor(3, 2, 0);
} else {
 x_417 = x_406;
 lean_ctor_set_tag(x_417, 3);
}
lean_ctor_set(x_417, 0, x_405);
lean_ctor_set(x_417, 1, x_407);
x_418 = l_Int_Linear_Expr_norm(x_417);
lean_dec_ref(x_417);
x_419 = l_Int_Linear_Poly_isUnsatLe(x_418);
if (x_419 == 0)
{
uint8_t x_420; 
x_420 = l_Int_Linear_Poly_isValidLe(x_418);
if (x_420 == 0)
{
lean_dec(x_409);
if (x_164 == 0)
{
lean_dec(x_415);
x_108 = x_416;
x_109 = x_408;
x_110 = x_418;
x_111 = x_407;
x_112 = x_405;
x_113 = x_410;
x_114 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_421; uint8_t x_422; 
lean_inc_ref(x_418);
x_421 = l_Int_Linear_Poly_toExpr(x_418);
x_422 = l_Int_Linear_instBEqExpr_beq(x_421, x_405);
lean_dec_ref(x_421);
if (x_422 == 0)
{
lean_dec(x_415);
x_108 = x_416;
x_109 = x_408;
x_110 = x_418;
x_111 = x_407;
x_112 = x_405;
x_113 = x_410;
x_114 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_423; uint8_t x_424; 
x_423 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35;
x_424 = l_Int_Linear_instBEqExpr_beq(x_407, x_423);
if (x_424 == 0)
{
lean_dec(x_415);
x_108 = x_416;
x_109 = x_408;
x_110 = x_418;
x_111 = x_407;
x_112 = x_405;
x_113 = x_410;
x_114 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_425; lean_object* x_426; 
lean_dec_ref(x_418);
lean_dec_ref(x_416);
lean_dec_ref(x_410);
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_405);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_425 = lean_box(0);
if (lean_is_scalar(x_415)) {
 x_426 = lean_alloc_ctor(0, 1, 0);
} else {
 x_426 = x_415;
}
lean_ctor_set(x_426, 0, x_425);
return x_426;
}
}
}
}
else
{
lean_object* x_427; 
lean_dec_ref(x_418);
lean_dec(x_415);
lean_dec_ref(x_410);
x_427 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_408, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 x_429 = x_427;
} else {
 lean_dec_ref(x_427);
 x_429 = lean_box(0);
}
x_430 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38;
x_431 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
x_432 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_405);
x_433 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_407);
x_434 = l_Lean_eagerReflBoolTrue;
x_435 = l_Lean_mkApp4(x_431, x_428, x_432, x_433, x_434);
x_436 = l_Lean_mkPropEq(x_416, x_430);
x_437 = l_Lean_Meta_mkExpectedPropHint(x_435, x_436);
if (lean_is_scalar(x_409)) {
 x_438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_438 = x_409;
}
lean_ctor_set(x_438, 0, x_430);
lean_ctor_set(x_438, 1, x_437);
x_439 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_439, 0, x_438);
if (lean_is_scalar(x_429)) {
 x_440 = lean_alloc_ctor(0, 1, 0);
} else {
 x_440 = x_429;
}
lean_ctor_set(x_440, 0, x_439);
return x_440;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec_ref(x_416);
lean_dec(x_409);
lean_dec(x_407);
lean_dec(x_405);
x_441 = lean_ctor_get(x_427, 0);
lean_inc(x_441);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 x_442 = x_427;
} else {
 lean_dec_ref(x_427);
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
lean_object* x_444; 
lean_dec_ref(x_418);
lean_dec(x_415);
lean_dec_ref(x_410);
x_444 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_408, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 x_446 = x_444;
} else {
 lean_dec_ref(x_444);
 x_446 = lean_box(0);
}
x_447 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8;
x_448 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
x_449 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_405);
x_450 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_407);
x_451 = l_Lean_eagerReflBoolTrue;
x_452 = l_Lean_mkApp4(x_448, x_445, x_449, x_450, x_451);
x_453 = l_Lean_mkPropEq(x_416, x_447);
x_454 = l_Lean_Meta_mkExpectedPropHint(x_452, x_453);
if (lean_is_scalar(x_409)) {
 x_455 = lean_alloc_ctor(0, 2, 0);
} else {
 x_455 = x_409;
}
lean_ctor_set(x_455, 0, x_447);
lean_ctor_set(x_455, 1, x_454);
x_456 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_456, 0, x_455);
if (lean_is_scalar(x_446)) {
 x_457 = lean_alloc_ctor(0, 1, 0);
} else {
 x_457 = x_446;
}
lean_ctor_set(x_457, 0, x_456);
return x_457;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec_ref(x_416);
lean_dec(x_409);
lean_dec(x_407);
lean_dec(x_405);
x_458 = lean_ctor_get(x_444, 0);
lean_inc(x_458);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 x_459 = x_444;
} else {
 lean_dec_ref(x_444);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(1, 1, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_458);
return x_460;
}
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_412);
lean_dec_ref(x_410);
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_461 = lean_ctor_get(x_413, 0);
lean_inc(x_461);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 x_462 = x_413;
} else {
 lean_dec_ref(x_413);
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
lean_dec_ref(x_410);
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_464 = lean_ctor_get(x_411, 0);
lean_inc(x_464);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 x_465 = x_411;
} else {
 lean_dec_ref(x_411);
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
}
else
{
lean_object* x_467; 
lean_dec(x_167);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_467 = lean_box(0);
lean_ctor_set(x_165, 0, x_467);
return x_165;
}
}
else
{
lean_object* x_468; 
x_468 = lean_ctor_get(x_165, 0);
lean_inc(x_468);
lean_dec(x_165);
if (lean_obj_tag(x_468) == 1)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 x_470 = x_468;
} else {
 lean_dec_ref(x_468);
 x_470 = lean_box(0);
}
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
x_472 = lean_ctor_get(x_469, 0);
lean_inc(x_472);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_473 = x_469;
} else {
 lean_dec_ref(x_469);
 x_473 = lean_box(0);
}
x_474 = lean_ctor_get(x_471, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_471, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 lean_ctor_release(x_471, 1);
 x_476 = x_471;
} else {
 lean_dec_ref(x_471);
 x_476 = lean_box(0);
}
lean_inc(x_475);
x_477 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_477, 0, x_163);
lean_closure_set(x_477, 1, x_475);
lean_inc(x_472);
lean_inc_ref(x_477);
x_478 = l_Int_Linear_Expr_denoteExpr___redArg(x_477, x_472);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; 
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
lean_dec_ref(x_478);
lean_inc(x_474);
lean_inc_ref(x_477);
x_480 = l_Int_Linear_Expr_denoteExpr___redArg(x_477, x_474);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 x_482 = x_480;
} else {
 lean_dec_ref(x_480);
 x_482 = lean_box(0);
}
x_483 = l_Lean_mkIntLE(x_479, x_481);
lean_inc(x_474);
lean_inc(x_472);
if (lean_is_scalar(x_473)) {
 x_484 = lean_alloc_ctor(3, 2, 0);
} else {
 x_484 = x_473;
 lean_ctor_set_tag(x_484, 3);
}
lean_ctor_set(x_484, 0, x_472);
lean_ctor_set(x_484, 1, x_474);
x_485 = l_Int_Linear_Expr_norm(x_484);
lean_dec_ref(x_484);
x_486 = l_Int_Linear_Poly_isUnsatLe(x_485);
if (x_486 == 0)
{
uint8_t x_487; 
x_487 = l_Int_Linear_Poly_isValidLe(x_485);
if (x_487 == 0)
{
lean_dec(x_476);
lean_dec(x_470);
if (x_164 == 0)
{
lean_dec(x_482);
x_108 = x_483;
x_109 = x_475;
x_110 = x_485;
x_111 = x_474;
x_112 = x_472;
x_113 = x_477;
x_114 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_488; uint8_t x_489; 
lean_inc_ref(x_485);
x_488 = l_Int_Linear_Poly_toExpr(x_485);
x_489 = l_Int_Linear_instBEqExpr_beq(x_488, x_472);
lean_dec_ref(x_488);
if (x_489 == 0)
{
lean_dec(x_482);
x_108 = x_483;
x_109 = x_475;
x_110 = x_485;
x_111 = x_474;
x_112 = x_472;
x_113 = x_477;
x_114 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_490; uint8_t x_491; 
x_490 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35;
x_491 = l_Int_Linear_instBEqExpr_beq(x_474, x_490);
if (x_491 == 0)
{
lean_dec(x_482);
x_108 = x_483;
x_109 = x_475;
x_110 = x_485;
x_111 = x_474;
x_112 = x_472;
x_113 = x_477;
x_114 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_492; lean_object* x_493; 
lean_dec_ref(x_485);
lean_dec_ref(x_483);
lean_dec_ref(x_477);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_472);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_492 = lean_box(0);
if (lean_is_scalar(x_482)) {
 x_493 = lean_alloc_ctor(0, 1, 0);
} else {
 x_493 = x_482;
}
lean_ctor_set(x_493, 0, x_492);
return x_493;
}
}
}
}
else
{
lean_object* x_494; 
lean_dec_ref(x_485);
lean_dec(x_482);
lean_dec_ref(x_477);
x_494 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_475, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 x_496 = x_494;
} else {
 lean_dec_ref(x_494);
 x_496 = lean_box(0);
}
x_497 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38;
x_498 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
x_499 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_472);
x_500 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_474);
x_501 = l_Lean_eagerReflBoolTrue;
x_502 = l_Lean_mkApp4(x_498, x_495, x_499, x_500, x_501);
x_503 = l_Lean_mkPropEq(x_483, x_497);
x_504 = l_Lean_Meta_mkExpectedPropHint(x_502, x_503);
if (lean_is_scalar(x_476)) {
 x_505 = lean_alloc_ctor(0, 2, 0);
} else {
 x_505 = x_476;
}
lean_ctor_set(x_505, 0, x_497);
lean_ctor_set(x_505, 1, x_504);
if (lean_is_scalar(x_470)) {
 x_506 = lean_alloc_ctor(1, 1, 0);
} else {
 x_506 = x_470;
}
lean_ctor_set(x_506, 0, x_505);
if (lean_is_scalar(x_496)) {
 x_507 = lean_alloc_ctor(0, 1, 0);
} else {
 x_507 = x_496;
}
lean_ctor_set(x_507, 0, x_506);
return x_507;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec_ref(x_483);
lean_dec(x_476);
lean_dec(x_474);
lean_dec(x_472);
lean_dec(x_470);
x_508 = lean_ctor_get(x_494, 0);
lean_inc(x_508);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 x_509 = x_494;
} else {
 lean_dec_ref(x_494);
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
lean_object* x_511; 
lean_dec_ref(x_485);
lean_dec(x_482);
lean_dec_ref(x_477);
x_511 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_475, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 x_513 = x_511;
} else {
 lean_dec_ref(x_511);
 x_513 = lean_box(0);
}
x_514 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8;
x_515 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
x_516 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_472);
x_517 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_474);
x_518 = l_Lean_eagerReflBoolTrue;
x_519 = l_Lean_mkApp4(x_515, x_512, x_516, x_517, x_518);
x_520 = l_Lean_mkPropEq(x_483, x_514);
x_521 = l_Lean_Meta_mkExpectedPropHint(x_519, x_520);
if (lean_is_scalar(x_476)) {
 x_522 = lean_alloc_ctor(0, 2, 0);
} else {
 x_522 = x_476;
}
lean_ctor_set(x_522, 0, x_514);
lean_ctor_set(x_522, 1, x_521);
if (lean_is_scalar(x_470)) {
 x_523 = lean_alloc_ctor(1, 1, 0);
} else {
 x_523 = x_470;
}
lean_ctor_set(x_523, 0, x_522);
if (lean_is_scalar(x_513)) {
 x_524 = lean_alloc_ctor(0, 1, 0);
} else {
 x_524 = x_513;
}
lean_ctor_set(x_524, 0, x_523);
return x_524;
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
lean_dec_ref(x_483);
lean_dec(x_476);
lean_dec(x_474);
lean_dec(x_472);
lean_dec(x_470);
x_525 = lean_ctor_get(x_511, 0);
lean_inc(x_525);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 x_526 = x_511;
} else {
 lean_dec_ref(x_511);
 x_526 = lean_box(0);
}
if (lean_is_scalar(x_526)) {
 x_527 = lean_alloc_ctor(1, 1, 0);
} else {
 x_527 = x_526;
}
lean_ctor_set(x_527, 0, x_525);
return x_527;
}
}
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_479);
lean_dec_ref(x_477);
lean_dec(x_476);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_473);
lean_dec(x_472);
lean_dec(x_470);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_528 = lean_ctor_get(x_480, 0);
lean_inc(x_528);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 x_529 = x_480;
} else {
 lean_dec_ref(x_480);
 x_529 = lean_box(0);
}
if (lean_is_scalar(x_529)) {
 x_530 = lean_alloc_ctor(1, 1, 0);
} else {
 x_530 = x_529;
}
lean_ctor_set(x_530, 0, x_528);
return x_530;
}
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec_ref(x_477);
lean_dec(x_476);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_473);
lean_dec(x_472);
lean_dec(x_470);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_531 = lean_ctor_get(x_478, 0);
lean_inc(x_531);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 x_532 = x_478;
} else {
 lean_dec_ref(x_478);
 x_532 = lean_box(0);
}
if (lean_is_scalar(x_532)) {
 x_533 = lean_alloc_ctor(1, 1, 0);
} else {
 x_533 = x_532;
}
lean_ctor_set(x_533, 0, x_531);
return x_533;
}
}
else
{
lean_object* x_534; lean_object* x_535; 
lean_dec(x_468);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_534 = lean_box(0);
x_535 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_535, 0, x_534);
return x_535;
}
}
}
else
{
uint8_t x_536; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_536 = !lean_is_exclusive(x_165);
if (x_536 == 0)
{
return x_165;
}
else
{
lean_object* x_537; lean_object* x_538; 
x_537 = lean_ctor_get(x_165, 0);
lean_inc(x_537);
lean_dec(x_165);
x_538 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_538, 0, x_537);
return x_538;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trans", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelOne;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ge", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30;
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_le_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_ge_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_lt_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_gt_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7;
x_64 = lean_unsigned_to_nat(1u);
x_65 = l_Lean_Expr_isAppOfArity(x_1, x_63, x_64);
if (x_65 == 0)
{
uint8_t x_66; lean_object* x_67; 
x_66 = 1;
x_67 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_1, x_66, x_2, x_3, x_4, x_5);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = l_Lean_Expr_appArg_x21(x_1);
x_69 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_68, x_3);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = l_Lean_Expr_cleanupAnnotations(x_70);
x_72 = l_Lean_Expr_isApp(x_71);
if (x_72 == 0)
{
lean_dec_ref(x_71);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_71, 1);
lean_inc_ref(x_73);
x_74 = l_Lean_Expr_appFnCleanup___redArg(x_71);
x_75 = l_Lean_Expr_isApp(x_74);
if (x_75 == 0)
{
lean_dec_ref(x_74);
lean_dec_ref(x_73);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_74, 1);
lean_inc_ref(x_76);
x_77 = l_Lean_Expr_appFnCleanup___redArg(x_74);
x_78 = l_Lean_Expr_isApp(x_77);
if (x_78 == 0)
{
lean_dec_ref(x_77);
lean_dec_ref(x_76);
lean_dec_ref(x_73);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_79; uint8_t x_80; 
x_79 = l_Lean_Expr_appFnCleanup___redArg(x_77);
x_80 = l_Lean_Expr_isApp(x_79);
if (x_80 == 0)
{
lean_dec_ref(x_79);
lean_dec_ref(x_76);
lean_dec_ref(x_73);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_79, 1);
lean_inc_ref(x_81);
x_82 = l_Lean_Expr_appFnCleanup___redArg(x_79);
x_83 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10;
x_84 = l_Lean_Expr_isConstOf(x_82, x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13;
x_86 = l_Lean_Expr_isConstOf(x_82, x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16;
x_88 = l_Lean_Expr_isConstOf(x_82, x_87);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17;
x_90 = l_Lean_Expr_isConstOf(x_82, x_89);
lean_dec_ref(x_82);
if (x_90 == 0)
{
lean_dec_ref(x_81);
lean_dec_ref(x_76);
lean_dec_ref(x_73);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_91; 
x_91 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_81, x_3);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
x_93 = l_Lean_Expr_cleanupAnnotations(x_92);
x_94 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
x_95 = l_Lean_Expr_isConstOf(x_93, x_94);
lean_dec_ref(x_93);
if (x_95 == 0)
{
lean_dec_ref(x_76);
lean_dec_ref(x_73);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17;
lean_inc_ref(x_73);
x_97 = l_Lean_mkIntAdd(x_73, x_96);
lean_inc_ref(x_76);
x_98 = l_Lean_mkIntLE(x_97, x_76);
x_99 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20;
x_100 = l_Lean_mkAppB(x_99, x_76, x_73);
x_11 = x_98;
x_12 = x_100;
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = lean_box(0);
goto block_62;
}
}
else
{
uint8_t x_101; 
lean_dec_ref(x_76);
lean_dec_ref(x_73);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_101 = !lean_is_exclusive(x_91);
if (x_101 == 0)
{
return x_91;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_91, 0);
lean_inc(x_102);
lean_dec(x_91);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
}
else
{
lean_object* x_104; 
lean_dec_ref(x_82);
x_104 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_81, x_3);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_106 = l_Lean_Expr_cleanupAnnotations(x_105);
x_107 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
x_108 = l_Lean_Expr_isConstOf(x_106, x_107);
lean_dec_ref(x_106);
if (x_108 == 0)
{
lean_dec_ref(x_76);
lean_dec_ref(x_73);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17;
lean_inc_ref(x_76);
x_110 = l_Lean_mkIntAdd(x_76, x_109);
lean_inc_ref(x_73);
x_111 = l_Lean_mkIntLE(x_110, x_73);
x_112 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23;
x_113 = l_Lean_mkAppB(x_112, x_76, x_73);
x_11 = x_111;
x_12 = x_113;
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = lean_box(0);
goto block_62;
}
}
else
{
uint8_t x_114; 
lean_dec_ref(x_76);
lean_dec_ref(x_73);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_114 = !lean_is_exclusive(x_104);
if (x_114 == 0)
{
return x_104;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_104, 0);
lean_inc(x_115);
lean_dec(x_104);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
}
}
else
{
lean_object* x_117; 
lean_dec_ref(x_82);
x_117 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_81, x_3);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = l_Lean_Expr_cleanupAnnotations(x_118);
x_120 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
x_121 = l_Lean_Expr_isConstOf(x_119, x_120);
lean_dec_ref(x_119);
if (x_121 == 0)
{
lean_dec_ref(x_76);
lean_dec_ref(x_73);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_inc_ref(x_76);
lean_inc_ref(x_73);
x_122 = l_Lean_mkIntLE(x_73, x_76);
x_123 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26;
x_124 = l_Lean_mkAppB(x_123, x_76, x_73);
x_11 = x_122;
x_12 = x_124;
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = lean_box(0);
goto block_62;
}
}
else
{
uint8_t x_125; 
lean_dec_ref(x_76);
lean_dec_ref(x_73);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_125 = !lean_is_exclusive(x_117);
if (x_125 == 0)
{
return x_117;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_117, 0);
lean_inc(x_126);
lean_dec(x_117);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
}
}
else
{
lean_object* x_128; 
lean_dec_ref(x_82);
x_128 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_81, x_3);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec_ref(x_128);
x_130 = l_Lean_Expr_cleanupAnnotations(x_129);
x_131 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
x_132 = l_Lean_Expr_isConstOf(x_130, x_131);
lean_dec_ref(x_130);
if (x_132 == 0)
{
lean_dec_ref(x_76);
lean_dec_ref(x_73);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_inc_ref(x_73);
lean_inc_ref(x_76);
x_133 = l_Lean_mkIntLE(x_76, x_73);
x_134 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29;
x_135 = l_Lean_mkAppB(x_134, x_76, x_73);
x_11 = x_133;
x_12 = x_135;
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = lean_box(0);
goto block_62;
}
}
else
{
uint8_t x_136; 
lean_dec_ref(x_76);
lean_dec_ref(x_73);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_136 = !lean_is_exclusive(x_128);
if (x_136 == 0)
{
return x_128;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_128, 0);
lean_inc(x_137);
lean_dec(x_128);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
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
uint8_t x_139; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_139 = !lean_is_exclusive(x_69);
if (x_139 == 0)
{
return x_69;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_69, 0);
lean_inc(x_140);
lean_dec(x_69);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
block_62:
{
uint8_t x_18; lean_object* x_19; 
x_18 = 0;
lean_inc_ref(x_11);
x_19 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_11, x_18, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
if (lean_obj_tag(x_21) == 1)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4;
x_28 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5;
lean_inc(x_25);
x_29 = l_Lean_mkApp6(x_27, x_28, x_1, x_11, x_25, x_12, x_26);
lean_ctor_set(x_23, 1, x_29);
return x_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4;
x_33 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5;
lean_inc(x_30);
x_34 = l_Lean_mkApp6(x_32, x_33, x_1, x_11, x_30, x_12, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_21, 0, x_35);
return x_19;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_21, 0);
lean_inc(x_36);
lean_dec(x_21);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4;
x_41 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5;
lean_inc(x_37);
x_42 = l_Lean_mkApp6(x_40, x_41, x_1, x_11, x_37, x_12, x_38);
if (lean_is_scalar(x_39)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_39;
}
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_19, 0, x_44);
return x_19;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_21);
lean_dec_ref(x_1);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_11);
lean_ctor_set(x_45, 1, x_12);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_19, 0, x_46);
return x_19;
}
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_19, 0);
lean_inc(x_47);
lean_dec(x_19);
if (lean_obj_tag(x_47) == 1)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
 x_52 = lean_box(0);
}
x_53 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4;
x_54 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5;
lean_inc(x_50);
x_55 = l_Lean_mkApp6(x_53, x_54, x_1, x_11, x_50, x_12, x_51);
if (lean_is_scalar(x_52)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_52;
}
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_55);
if (lean_is_scalar(x_49)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_49;
}
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_47);
lean_dec_ref(x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_11);
lean_ctor_set(x_59, 1, x_12);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_1);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_dvd_gcd", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_dvd", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dvd_eq_false", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_30; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_30 = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_80; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_39 = x_35;
} else {
 lean_dec_ref(x_35);
 x_39 = lean_box(0);
}
x_40 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5;
x_80 = lean_int_dec_eq(x_36, x_40);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_free_object(x_30);
x_81 = l_Lean_instInhabitedExpr;
lean_inc(x_38);
x_82 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_82, 0, x_81);
lean_closure_set(x_82, 1, x_38);
lean_inc(x_37);
lean_inc_ref(x_82);
x_83 = l_Int_Linear_Expr_denoteExpr___redArg(x_82, x_37);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_141; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_141 = lean_int_dec_le(x_40, x_36);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_142 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17;
x_143 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
x_144 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22;
x_145 = lean_int_neg(x_36);
x_146 = l_Int_toNat(x_145);
lean_dec(x_145);
x_147 = l_Lean_instToExprInt_mkNat(x_146);
x_148 = l_Lean_mkApp3(x_142, x_143, x_144, x_147);
x_86 = x_148;
goto block_140;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = l_Int_toNat(x_36);
x_150 = l_Lean_instToExprInt_mkNat(x_149);
x_86 = x_150;
goto block_140;
}
block_140:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_inc_ref(x_86);
x_87 = l_Lean_mkIntDvd(x_86, x_84);
x_88 = l_Int_Linear_Expr_norm(x_37);
lean_inc(x_36);
x_89 = l_Int_Linear_Poly_gcdCoeffs(x_88, x_36);
x_90 = l_Int_Linear_Poly_getConst(x_88);
x_91 = lean_int_emod(x_90, x_89);
lean_dec(x_90);
x_92 = lean_int_dec_eq(x_91, x_40);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; 
lean_dec(x_89);
lean_dec_ref(x_88);
lean_dec(x_85);
lean_dec_ref(x_82);
lean_dec(x_36);
x_93 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_38, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8;
x_97 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8;
x_98 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_37);
x_99 = l_Lean_eagerReflBoolTrue;
x_100 = l_Lean_mkApp4(x_97, x_95, x_86, x_98, x_99);
x_101 = l_Lean_mkPropEq(x_87, x_96);
x_102 = l_Lean_Meta_mkExpectedPropHint(x_100, x_101);
if (lean_is_scalar(x_39)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_39;
}
lean_ctor_set(x_103, 0, x_96);
lean_ctor_set(x_103, 1, x_102);
if (lean_is_scalar(x_34)) {
 x_104 = lean_alloc_ctor(1, 1, 0);
} else {
 x_104 = x_34;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_93, 0, x_104);
return x_93;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_105 = lean_ctor_get(x_93, 0);
lean_inc(x_105);
lean_dec(x_93);
x_106 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8;
x_107 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8;
x_108 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_37);
x_109 = l_Lean_eagerReflBoolTrue;
x_110 = l_Lean_mkApp4(x_107, x_105, x_86, x_108, x_109);
x_111 = l_Lean_mkPropEq(x_87, x_106);
x_112 = l_Lean_Meta_mkExpectedPropHint(x_110, x_111);
if (lean_is_scalar(x_39)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_39;
}
lean_ctor_set(x_113, 0, x_106);
lean_ctor_set(x_113, 1, x_112);
if (lean_is_scalar(x_34)) {
 x_114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_114 = x_34;
}
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
else
{
uint8_t x_116; 
lean_dec_ref(x_87);
lean_dec_ref(x_86);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_34);
x_116 = !lean_is_exclusive(x_93);
if (x_116 == 0)
{
return x_93;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_93, 0);
lean_inc(x_117);
lean_dec(x_93);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_39);
lean_dec(x_34);
x_119 = l_Int_Linear_Poly_div(x_89, x_88);
lean_inc_ref(x_119);
x_120 = l_Int_Linear_Poly_toExpr(x_119);
x_121 = l_Int_Linear_instBEqExpr_beq(x_37, x_120);
lean_dec_ref(x_120);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_85);
lean_inc_ref(x_119);
x_122 = l_Int_Linear_Poly_denoteExpr___redArg(x_82, x_119);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec_ref(x_122);
x_124 = lean_int_ediv(x_36, x_89);
lean_dec(x_36);
x_125 = lean_int_dec_le(x_40, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_126 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17;
x_127 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
x_128 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22;
x_129 = lean_int_neg(x_124);
lean_dec(x_124);
x_130 = l_Int_toNat(x_129);
lean_dec(x_129);
x_131 = l_Lean_instToExprInt_mkNat(x_130);
x_132 = l_Lean_mkApp3(x_126, x_127, x_128, x_131);
x_41 = x_123;
x_42 = x_89;
x_43 = x_119;
x_44 = lean_box(0);
x_45 = x_86;
x_46 = x_87;
x_47 = x_132;
goto block_79;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = l_Int_toNat(x_124);
lean_dec(x_124);
x_134 = l_Lean_instToExprInt_mkNat(x_133);
x_41 = x_123;
x_42 = x_89;
x_43 = x_119;
x_44 = lean_box(0);
x_45 = x_86;
x_46 = x_87;
x_47 = x_134;
goto block_79;
}
}
else
{
uint8_t x_135; 
lean_dec_ref(x_119);
lean_dec(x_89);
lean_dec_ref(x_87);
lean_dec_ref(x_86);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_135 = !lean_is_exclusive(x_122);
if (x_135 == 0)
{
return x_122;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_122, 0);
lean_inc(x_136);
lean_dec(x_122);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec_ref(x_119);
lean_dec(x_89);
lean_dec_ref(x_87);
lean_dec_ref(x_86);
lean_dec_ref(x_82);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_138 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_139 = lean_alloc_ctor(0, 1, 0);
} else {
 x_139 = x_85;
}
lean_ctor_set(x_139, 0, x_138);
return x_139;
}
}
}
}
else
{
uint8_t x_151; 
lean_dec_ref(x_82);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_151 = !lean_is_exclusive(x_83);
if (x_151 == 0)
{
return x_83;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_83, 0);
lean_inc(x_152);
lean_dec(x_83);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
}
}
else
{
lean_object* x_154; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_154 = lean_box(0);
lean_ctor_set(x_30, 0, x_154);
return x_30;
}
block_79:
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_inc_ref(x_47);
x_48 = l_Lean_mkIntDvd(x_47, x_41);
x_49 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30;
x_50 = lean_int_dec_eq(x_42, x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_38, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2;
x_54 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_37);
x_55 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_43);
x_56 = lean_int_dec_le(x_40, x_42);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17;
x_58 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
x_59 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22;
x_60 = lean_int_neg(x_42);
lean_dec(x_42);
x_61 = l_Int_toNat(x_60);
lean_dec(x_60);
x_62 = l_Lean_instToExprInt_mkNat(x_61);
x_63 = l_Lean_mkApp3(x_57, x_58, x_59, x_62);
x_17 = x_55;
x_18 = x_54;
x_19 = x_48;
x_20 = x_52;
x_21 = x_47;
x_22 = lean_box(0);
x_23 = x_45;
x_24 = x_46;
x_25 = x_53;
x_26 = x_63;
goto block_29;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Int_toNat(x_42);
lean_dec(x_42);
x_65 = l_Lean_instToExprInt_mkNat(x_64);
x_17 = x_55;
x_18 = x_54;
x_19 = x_48;
x_20 = x_52;
x_21 = x_47;
x_22 = lean_box(0);
x_23 = x_45;
x_24 = x_46;
x_25 = x_53;
x_26 = x_65;
goto block_29;
}
}
else
{
uint8_t x_66; 
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_37);
x_66 = !lean_is_exclusive(x_51);
if (x_66 == 0)
{
return x_51;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_51, 0);
lean_inc(x_67);
lean_dec(x_51);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; 
lean_dec_ref(x_47);
lean_dec(x_42);
x_69 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_38, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5;
x_72 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_37);
x_73 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_43);
x_74 = l_Lean_eagerReflBoolTrue;
x_75 = l_Lean_mkApp5(x_71, x_70, x_45, x_72, x_73, x_74);
x_7 = x_48;
x_8 = x_46;
x_9 = x_75;
x_10 = lean_box(0);
goto block_16;
}
else
{
uint8_t x_76; 
lean_dec_ref(x_48);
lean_dec_ref(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_43);
lean_dec(x_37);
x_76 = !lean_is_exclusive(x_69);
if (x_76 == 0)
{
return x_69;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_69, 0);
lean_inc(x_77);
lean_dec(x_69);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
}
}
else
{
lean_object* x_155; 
lean_dec(x_32);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_155 = lean_box(0);
lean_ctor_set(x_30, 0, x_155);
return x_30;
}
}
else
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_30, 0);
lean_inc(x_156);
lean_dec(x_30);
if (lean_obj_tag(x_156) == 1)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_204; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_157, 0);
lean_inc(x_160);
lean_dec(x_157);
x_161 = lean_ctor_get(x_159, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_163 = x_159;
} else {
 lean_dec_ref(x_159);
 x_163 = lean_box(0);
}
x_164 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5;
x_204 = lean_int_dec_eq(x_160, x_164);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = l_Lean_instInhabitedExpr;
lean_inc(x_162);
x_206 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_206, 0, x_205);
lean_closure_set(x_206, 1, x_162);
lean_inc(x_161);
lean_inc_ref(x_206);
x_207 = l_Int_Linear_Expr_denoteExpr___redArg(x_206, x_161);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_255; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 x_209 = x_207;
} else {
 lean_dec_ref(x_207);
 x_209 = lean_box(0);
}
x_255 = lean_int_dec_le(x_164, x_160);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_256 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17;
x_257 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
x_258 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22;
x_259 = lean_int_neg(x_160);
x_260 = l_Int_toNat(x_259);
lean_dec(x_259);
x_261 = l_Lean_instToExprInt_mkNat(x_260);
x_262 = l_Lean_mkApp3(x_256, x_257, x_258, x_261);
x_210 = x_262;
goto block_254;
}
else
{
lean_object* x_263; lean_object* x_264; 
x_263 = l_Int_toNat(x_160);
x_264 = l_Lean_instToExprInt_mkNat(x_263);
x_210 = x_264;
goto block_254;
}
block_254:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
lean_inc_ref(x_210);
x_211 = l_Lean_mkIntDvd(x_210, x_208);
x_212 = l_Int_Linear_Expr_norm(x_161);
lean_inc(x_160);
x_213 = l_Int_Linear_Poly_gcdCoeffs(x_212, x_160);
x_214 = l_Int_Linear_Poly_getConst(x_212);
x_215 = lean_int_emod(x_214, x_213);
lean_dec(x_214);
x_216 = lean_int_dec_eq(x_215, x_164);
lean_dec(x_215);
if (x_216 == 0)
{
lean_object* x_217; 
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec(x_209);
lean_dec_ref(x_206);
lean_dec(x_160);
x_217 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_162, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 x_219 = x_217;
} else {
 lean_dec_ref(x_217);
 x_219 = lean_box(0);
}
x_220 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8;
x_221 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8;
x_222 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_161);
x_223 = l_Lean_eagerReflBoolTrue;
x_224 = l_Lean_mkApp4(x_221, x_218, x_210, x_222, x_223);
x_225 = l_Lean_mkPropEq(x_211, x_220);
x_226 = l_Lean_Meta_mkExpectedPropHint(x_224, x_225);
if (lean_is_scalar(x_163)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_163;
}
lean_ctor_set(x_227, 0, x_220);
lean_ctor_set(x_227, 1, x_226);
if (lean_is_scalar(x_158)) {
 x_228 = lean_alloc_ctor(1, 1, 0);
} else {
 x_228 = x_158;
}
lean_ctor_set(x_228, 0, x_227);
if (lean_is_scalar(x_219)) {
 x_229 = lean_alloc_ctor(0, 1, 0);
} else {
 x_229 = x_219;
}
lean_ctor_set(x_229, 0, x_228);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec_ref(x_211);
lean_dec_ref(x_210);
lean_dec(x_163);
lean_dec(x_161);
lean_dec(x_158);
x_230 = lean_ctor_get(x_217, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 x_231 = x_217;
} else {
 lean_dec_ref(x_217);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 1, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_230);
return x_232;
}
}
else
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; 
lean_dec(x_163);
lean_dec(x_158);
x_233 = l_Int_Linear_Poly_div(x_213, x_212);
lean_inc_ref(x_233);
x_234 = l_Int_Linear_Poly_toExpr(x_233);
x_235 = l_Int_Linear_instBEqExpr_beq(x_161, x_234);
lean_dec_ref(x_234);
if (x_235 == 0)
{
lean_object* x_236; 
lean_dec(x_209);
lean_inc_ref(x_233);
x_236 = l_Int_Linear_Poly_denoteExpr___redArg(x_206, x_233);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
lean_dec_ref(x_236);
x_238 = lean_int_ediv(x_160, x_213);
lean_dec(x_160);
x_239 = lean_int_dec_le(x_164, x_238);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_240 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17;
x_241 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
x_242 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22;
x_243 = lean_int_neg(x_238);
lean_dec(x_238);
x_244 = l_Int_toNat(x_243);
lean_dec(x_243);
x_245 = l_Lean_instToExprInt_mkNat(x_244);
x_246 = l_Lean_mkApp3(x_240, x_241, x_242, x_245);
x_165 = x_237;
x_166 = x_213;
x_167 = x_233;
x_168 = lean_box(0);
x_169 = x_210;
x_170 = x_211;
x_171 = x_246;
goto block_203;
}
else
{
lean_object* x_247; lean_object* x_248; 
x_247 = l_Int_toNat(x_238);
lean_dec(x_238);
x_248 = l_Lean_instToExprInt_mkNat(x_247);
x_165 = x_237;
x_166 = x_213;
x_167 = x_233;
x_168 = lean_box(0);
x_169 = x_210;
x_170 = x_211;
x_171 = x_248;
goto block_203;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec_ref(x_233);
lean_dec(x_213);
lean_dec_ref(x_211);
lean_dec_ref(x_210);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_249 = lean_ctor_get(x_236, 0);
lean_inc(x_249);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 x_250 = x_236;
} else {
 lean_dec_ref(x_236);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 1, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_249);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; 
lean_dec_ref(x_233);
lean_dec(x_213);
lean_dec_ref(x_211);
lean_dec_ref(x_210);
lean_dec_ref(x_206);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_252 = lean_box(0);
if (lean_is_scalar(x_209)) {
 x_253 = lean_alloc_ctor(0, 1, 0);
} else {
 x_253 = x_209;
}
lean_ctor_set(x_253, 0, x_252);
return x_253;
}
}
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec_ref(x_206);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_265 = lean_ctor_get(x_207, 0);
lean_inc(x_265);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 x_266 = x_207;
} else {
 lean_dec_ref(x_207);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 1, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_265);
return x_267;
}
}
else
{
lean_object* x_268; lean_object* x_269; 
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_268 = lean_box(0);
x_269 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_269, 0, x_268);
return x_269;
}
block_203:
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; 
lean_inc_ref(x_171);
x_172 = l_Lean_mkIntDvd(x_171, x_165);
x_173 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30;
x_174 = lean_int_dec_eq(x_166, x_173);
if (x_174 == 0)
{
lean_object* x_175; 
x_175 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_162, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
x_177 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2;
x_178 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_161);
x_179 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_167);
x_180 = lean_int_dec_le(x_164, x_166);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_181 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17;
x_182 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
x_183 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22;
x_184 = lean_int_neg(x_166);
lean_dec(x_166);
x_185 = l_Int_toNat(x_184);
lean_dec(x_184);
x_186 = l_Lean_instToExprInt_mkNat(x_185);
x_187 = l_Lean_mkApp3(x_181, x_182, x_183, x_186);
x_17 = x_179;
x_18 = x_178;
x_19 = x_172;
x_20 = x_176;
x_21 = x_171;
x_22 = lean_box(0);
x_23 = x_169;
x_24 = x_170;
x_25 = x_177;
x_26 = x_187;
goto block_29;
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = l_Int_toNat(x_166);
lean_dec(x_166);
x_189 = l_Lean_instToExprInt_mkNat(x_188);
x_17 = x_179;
x_18 = x_178;
x_19 = x_172;
x_20 = x_176;
x_21 = x_171;
x_22 = lean_box(0);
x_23 = x_169;
x_24 = x_170;
x_25 = x_177;
x_26 = x_189;
goto block_29;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec_ref(x_172);
lean_dec_ref(x_171);
lean_dec_ref(x_170);
lean_dec_ref(x_169);
lean_dec_ref(x_167);
lean_dec(x_166);
lean_dec(x_161);
x_190 = lean_ctor_get(x_175, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_191 = x_175;
} else {
 lean_dec_ref(x_175);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 1, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_190);
return x_192;
}
}
else
{
lean_object* x_193; 
lean_dec_ref(x_171);
lean_dec(x_166);
x_193 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_162, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec_ref(x_193);
x_195 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5;
x_196 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_161);
x_197 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_167);
x_198 = l_Lean_eagerReflBoolTrue;
x_199 = l_Lean_mkApp5(x_195, x_194, x_169, x_196, x_197, x_198);
x_7 = x_172;
x_8 = x_170;
x_9 = x_199;
x_10 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec_ref(x_172);
lean_dec_ref(x_170);
lean_dec_ref(x_169);
lean_dec_ref(x_167);
lean_dec(x_161);
x_200 = lean_ctor_get(x_193, 0);
lean_inc(x_200);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 x_201 = x_193;
} else {
 lean_dec_ref(x_193);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 1, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_200);
return x_202;
}
}
}
}
else
{
lean_object* x_270; lean_object* x_271; 
lean_dec(x_156);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_270 = lean_box(0);
x_271 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_271, 0, x_270);
return x_271;
}
}
}
else
{
uint8_t x_272; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_272 = !lean_is_exclusive(x_30);
if (x_272 == 0)
{
return x_30;
}
else
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_30, 0);
lean_inc(x_273);
lean_dec(x_30);
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_273);
return x_274;
}
}
block_16:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc_ref(x_7);
x_11 = l_Lean_mkPropEq(x_8, x_7);
x_12 = l_Lean_Meta_mkExpectedPropHint(x_9, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
block_29:
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_eagerReflBoolTrue;
x_28 = l_Lean_mkApp7(x_25, x_20, x_23, x_18, x_21, x_17, x_26, x_27);
x_7 = x_19;
x_8 = x_24;
x_9 = x_28;
x_10 = lean_box(0);
goto block_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_instInhabitedExpr;
x_4 = lean_array_get_borrowed(x_3, x_1, x_2);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expr", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_of_norm_eq", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_7 = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Int_Linear_Expr_norm(x_11);
lean_inc_ref(x_13);
x_14 = l_Int_Linear_Poly_toExpr(x_13);
x_15 = l_Int_Linear_instBEqExpr_beq(x_11, x_14);
lean_dec_ref(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_free_object(x_7);
lean_inc(x_12);
x_16 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_12, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_18, 0, x_12);
lean_inc(x_11);
x_19 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_11);
lean_inc_ref(x_18);
x_20 = l_Int_Linear_Expr_denoteExpr___redArg(x_18, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc_ref(x_13);
x_22 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_13);
x_23 = l_Int_Linear_Poly_denoteExpr___redArg(x_18, x_13);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3;
x_27 = l_Lean_eagerReflBoolTrue;
x_28 = l_Lean_mkApp4(x_26, x_17, x_19, x_22, x_27);
lean_inc(x_25);
x_29 = l_Lean_mkIntEq(x_21, x_25);
x_30 = l_Lean_Meta_mkExpectedPropHint(x_28, x_29);
lean_ctor_set(x_9, 1, x_30);
lean_ctor_set(x_9, 0, x_25);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_23, 0, x_31);
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
x_33 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3;
x_34 = l_Lean_eagerReflBoolTrue;
x_35 = l_Lean_mkApp4(x_33, x_17, x_19, x_22, x_34);
lean_inc(x_32);
x_36 = l_Lean_mkIntEq(x_21, x_32);
x_37 = l_Lean_Meta_mkExpectedPropHint(x_35, x_36);
lean_ctor_set(x_9, 1, x_37);
lean_ctor_set(x_9, 0, x_32);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_9);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_free_object(x_9);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
return x_23;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_23, 0);
lean_inc(x_41);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_free_object(x_9);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_20, 0);
lean_inc(x_44);
lean_dec(x_20);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec_ref(x_13);
lean_free_object(x_9);
lean_dec(x_12);
lean_dec(x_11);
x_46 = !lean_is_exclusive(x_16);
if (x_46 == 0)
{
return x_16;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_16, 0);
lean_inc(x_47);
lean_dec(x_16);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; 
lean_dec_ref(x_13);
lean_free_object(x_9);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_49 = lean_box(0);
lean_ctor_set(x_7, 0, x_49);
return x_7;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_9, 0);
x_51 = lean_ctor_get(x_9, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_9);
x_52 = l_Int_Linear_Expr_norm(x_50);
lean_inc_ref(x_52);
x_53 = l_Int_Linear_Poly_toExpr(x_52);
x_54 = l_Int_Linear_instBEqExpr_beq(x_50, x_53);
lean_dec_ref(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_free_object(x_7);
lean_inc(x_51);
x_55 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_51, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_57, 0, x_51);
lean_inc(x_50);
x_58 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_50);
lean_inc_ref(x_57);
x_59 = l_Int_Linear_Expr_denoteExpr___redArg(x_57, x_50);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
lean_inc_ref(x_52);
x_61 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_52);
x_62 = l_Int_Linear_Poly_denoteExpr___redArg(x_57, x_52);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3;
x_66 = l_Lean_eagerReflBoolTrue;
x_67 = l_Lean_mkApp4(x_65, x_56, x_58, x_61, x_66);
lean_inc(x_63);
x_68 = l_Lean_mkIntEq(x_60, x_63);
x_69 = l_Lean_Meta_mkExpectedPropHint(x_67, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
if (lean_is_scalar(x_64)) {
 x_72 = lean_alloc_ctor(0, 1, 0);
} else {
 x_72 = x_64;
}
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_58);
lean_dec(x_56);
x_73 = lean_ctor_get(x_62, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_74 = x_62;
} else {
 lean_dec_ref(x_62);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec_ref(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_52);
x_76 = lean_ctor_get(x_59, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_77 = x_59;
} else {
 lean_dec_ref(x_59);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 1, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec(x_50);
x_79 = lean_ctor_get(x_55, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_80 = x_55;
} else {
 lean_dec_ref(x_55);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_79);
return x_81;
}
}
else
{
lean_object* x_82; 
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_82 = lean_box(0);
lean_ctor_set(x_7, 0, x_82);
return x_7;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_83 = lean_ctor_get(x_7, 0);
lean_inc(x_83);
lean_dec(x_7);
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
x_87 = l_Int_Linear_Expr_norm(x_84);
lean_inc_ref(x_87);
x_88 = l_Int_Linear_Poly_toExpr(x_87);
x_89 = l_Int_Linear_instBEqExpr_beq(x_84, x_88);
lean_dec_ref(x_88);
if (x_89 == 0)
{
lean_object* x_90; 
lean_inc(x_85);
x_90 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_85, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec_ref(x_90);
x_92 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_92, 0, x_85);
lean_inc(x_84);
x_93 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_84);
lean_inc_ref(x_92);
x_94 = l_Int_Linear_Expr_denoteExpr___redArg(x_92, x_84);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
lean_inc_ref(x_87);
x_96 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_87);
x_97 = l_Int_Linear_Poly_denoteExpr___redArg(x_92, x_87);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3;
x_101 = l_Lean_eagerReflBoolTrue;
x_102 = l_Lean_mkApp4(x_100, x_91, x_93, x_96, x_101);
lean_inc(x_98);
x_103 = l_Lean_mkIntEq(x_95, x_98);
x_104 = l_Lean_Meta_mkExpectedPropHint(x_102, x_103);
if (lean_is_scalar(x_86)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_86;
}
lean_ctor_set(x_105, 0, x_98);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
if (lean_is_scalar(x_99)) {
 x_107 = lean_alloc_ctor(0, 1, 0);
} else {
 x_107 = x_99;
}
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_93);
lean_dec(x_91);
lean_dec(x_86);
x_108 = lean_ctor_get(x_97, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_109 = x_97;
} else {
 lean_dec_ref(x_97);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_87);
lean_dec(x_86);
x_111 = lean_ctor_get(x_94, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_112 = x_94;
} else {
 lean_dec_ref(x_94);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
x_114 = lean_ctor_get(x_90, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_115 = x_90;
} else {
 lean_dec_ref(x_90);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_119 = !lean_is_exclusive(x_7);
if (x_119 == 0)
{
return x_7;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_7, 0);
lean_inc(x_120);
lean_dec(x_7);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8);
l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0);
l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
