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
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__1;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_instBEqExpr_beq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6;
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__0;
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0;
lean_object* l_Lean_mkIntLE(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__20;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2;
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__16;
lean_object* l_Lean_mkSort(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__18;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__4;
uint8_t l_Int_Linear_Poly_isUnsatEq(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__11;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__25;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatLe(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_denoteExpr___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__24;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1;
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__5;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntDvd(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__15;
lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Simp_Arith_Int_simpEq_x3f_spec__0(lean_object*);
lean_object* l_Lean_mkIntEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__19;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll___boxed(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__21;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__9;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__23;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__26;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__5;
lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19;
uint8_t l_Int_Linear_Poly_isValidLe(lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Expr_norm(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27___boxed(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6;
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14;
lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
lean_object* l_Int_Linear_Poly_toExpr(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__8;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__1;
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_withAbstractAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll(lean_object*);
extern lean_object* l_Lean_levelOne;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__1;
uint8_t l_Int_Linear_Poly_isValidEq(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10;
lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__22;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__12;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10;
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5;
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Expr_denoteExpr___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18;
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
lean_inc_ref(x_4);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_eagerReflBoolTrue;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Linear", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_eq_var_const", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__5;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_eq_false_of_divCoeff", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__9;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__8;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__12;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instNegInt", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_eq_coeff", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_eq", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__18;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_eq_var", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("True", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__22;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__23;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_eq_true", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_eq_false", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_5);
lean_inc_ref(x_2);
lean_inc_ref(x_11);
x_12 = l_Int_Linear_Expr_denoteExpr___redArg(x_11, x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_14 = x_12;
} else {
 lean_dec_ref(x_12);
 x_14 = lean_box(0);
}
lean_inc_ref(x_3);
lean_inc_ref(x_11);
x_15 = l_Int_Linear_Expr_denoteExpr___redArg(x_11, x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_213; uint8_t x_319; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_17 = x_15;
} else {
 lean_dec_ref(x_15);
 x_17 = lean_box(0);
}
x_18 = l_Lean_mkIntEq(x_13, x_16);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_92 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_92, 0, x_2);
lean_ctor_set(x_92, 1, x_3);
x_93 = l_Int_Linear_Expr_norm(x_92);
lean_dec_ref(x_92);
x_319 = l_Int_Linear_Poly_isUnsatEq(x_93);
if (x_319 == 0)
{
uint8_t x_320; 
x_320 = l_Int_Linear_Poly_isValidEq(x_93);
if (x_320 == 0)
{
lean_object* x_321; uint8_t x_322; 
lean_inc_ref(x_93);
x_321 = l_Int_Linear_Poly_toExpr(x_93);
x_322 = l_Int_Linear_instBEqExpr_beq(x_321, x_2);
lean_dec_ref(x_321);
if (x_322 == 0)
{
x_213 = x_322;
goto block_318;
}
else
{
lean_object* x_323; uint8_t x_324; 
x_323 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__21;
x_324 = l_Int_Linear_instBEqExpr_beq(x_3, x_323);
x_213 = x_324;
goto block_318;
}
}
else
{
lean_object* x_325; 
lean_dec_ref(x_93);
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_1);
x_325 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_325) == 0)
{
uint8_t x_326; 
x_326 = !lean_is_exclusive(x_325);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_327 = lean_ctor_get(x_325, 0);
x_328 = lean_box(0);
x_329 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__24;
x_330 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_331 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__25;
x_332 = l_Lean_Name_mkStr3(x_4, x_330, x_331);
x_333 = l_Lean_mkConst(x_332, x_328);
x_334 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_335 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_336 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_337 = l_Lean_mkApp4(x_333, x_327, x_334, x_335, x_336);
x_338 = l_Lean_mkPropEq(x_18, x_329);
x_339 = l_Lean_Meta_mkExpectedPropHint(x_337, x_338);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_329);
lean_ctor_set(x_340, 1, x_339);
x_341 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_325, 0, x_341);
return x_325;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_342 = lean_ctor_get(x_325, 0);
lean_inc(x_342);
lean_dec(x_325);
x_343 = lean_box(0);
x_344 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__24;
x_345 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_346 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__25;
x_347 = l_Lean_Name_mkStr3(x_4, x_345, x_346);
x_348 = l_Lean_mkConst(x_347, x_343);
x_349 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_350 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_351 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_352 = l_Lean_mkApp4(x_348, x_342, x_349, x_350, x_351);
x_353 = l_Lean_mkPropEq(x_18, x_344);
x_354 = l_Lean_Meta_mkExpectedPropHint(x_352, x_353);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_344);
lean_ctor_set(x_355, 1, x_354);
x_356 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_356, 0, x_355);
x_357 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_357, 0, x_356);
return x_357;
}
}
else
{
uint8_t x_358; 
lean_dec_ref(x_18);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_358 = !lean_is_exclusive(x_325);
if (x_358 == 0)
{
return x_325;
}
else
{
lean_object* x_359; lean_object* x_360; 
x_359 = lean_ctor_get(x_325, 0);
lean_inc(x_359);
lean_dec(x_325);
x_360 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_360, 0, x_359);
return x_360;
}
}
}
}
else
{
lean_object* x_361; 
lean_dec_ref(x_93);
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_1);
x_361 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_361) == 0)
{
uint8_t x_362; 
x_362 = !lean_is_exclusive(x_361);
if (x_362 == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_363 = lean_ctor_get(x_361, 0);
x_364 = lean_box(0);
x_365 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6;
x_366 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_367 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__26;
x_368 = l_Lean_Name_mkStr3(x_4, x_366, x_367);
x_369 = l_Lean_mkConst(x_368, x_364);
x_370 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_371 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_372 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_373 = l_Lean_mkApp4(x_369, x_363, x_370, x_371, x_372);
x_374 = l_Lean_mkPropEq(x_18, x_365);
x_375 = l_Lean_Meta_mkExpectedPropHint(x_373, x_374);
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_365);
lean_ctor_set(x_376, 1, x_375);
x_377 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_361, 0, x_377);
return x_361;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_378 = lean_ctor_get(x_361, 0);
lean_inc(x_378);
lean_dec(x_361);
x_379 = lean_box(0);
x_380 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6;
x_381 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_382 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__26;
x_383 = l_Lean_Name_mkStr3(x_4, x_381, x_382);
x_384 = l_Lean_mkConst(x_383, x_379);
x_385 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_386 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_387 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_388 = l_Lean_mkApp4(x_384, x_378, x_385, x_386, x_387);
x_389 = l_Lean_mkPropEq(x_18, x_380);
x_390 = l_Lean_Meta_mkExpectedPropHint(x_388, x_389);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_380);
lean_ctor_set(x_391, 1, x_390);
x_392 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_392, 0, x_391);
x_393 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_393, 0, x_392);
return x_393;
}
}
else
{
uint8_t x_394; 
lean_dec_ref(x_18);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_394 = !lean_is_exclusive(x_361);
if (x_394 == 0)
{
return x_361;
}
else
{
lean_object* x_395; lean_object* x_396; 
x_395 = lean_ctor_get(x_361, 0);
lean_inc(x_395);
lean_dec(x_361);
x_396 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_396, 0, x_395);
return x_396;
}
}
}
block_33:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_27 = l_Lean_mkApp5(x_19, x_24, x_22, x_23, x_25, x_26);
lean_inc_ref(x_21);
x_28 = l_Lean_mkPropEq(x_18, x_21);
x_29 = l_Lean_Meta_mkExpectedPropHint(x_27, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
if (lean_is_scalar(x_17)) {
 x_32 = lean_alloc_ctor(0, 1, 0);
} else {
 x_32 = x_17;
}
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
block_49:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_43 = l_Lean_mkApp6(x_39, x_35, x_34, x_37, x_40, x_41, x_42);
lean_inc_ref(x_38);
x_44 = l_Lean_mkPropEq(x_18, x_38);
x_45 = l_Lean_Meta_mkExpectedPropHint(x_43, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
if (lean_is_scalar(x_14)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_14;
}
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
block_91:
{
lean_object* x_53; 
x_53 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc_ref(x_52);
x_56 = l_Lean_mkIntEq(x_50, x_52);
x_57 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_58 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__2;
x_59 = l_Lean_Name_mkStr3(x_4, x_57, x_58);
x_60 = lean_box(0);
x_61 = l_Lean_mkConst(x_59, x_60);
x_62 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_63 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_64 = l_Lean_mkNatLit(x_51);
x_65 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_66 = l_Lean_mkApp6(x_61, x_55, x_62, x_63, x_64, x_52, x_65);
lean_inc_ref(x_56);
x_67 = l_Lean_mkPropEq(x_18, x_56);
x_68 = l_Lean_Meta_mkExpectedPropHint(x_66, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_56);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_53, 0, x_70);
return x_53;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_71 = lean_ctor_get(x_53, 0);
lean_inc(x_71);
lean_dec(x_53);
lean_inc_ref(x_52);
x_72 = l_Lean_mkIntEq(x_50, x_52);
x_73 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_74 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__2;
x_75 = l_Lean_Name_mkStr3(x_4, x_73, x_74);
x_76 = lean_box(0);
x_77 = l_Lean_mkConst(x_75, x_76);
x_78 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_79 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_80 = l_Lean_mkNatLit(x_51);
x_81 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_82 = l_Lean_mkApp6(x_77, x_71, x_78, x_79, x_80, x_52, x_81);
lean_inc_ref(x_72);
x_83 = l_Lean_mkPropEq(x_18, x_72);
x_84 = l_Lean_Meta_mkExpectedPropHint(x_82, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_72);
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
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_88 = !lean_is_exclusive(x_53);
if (x_88 == 0)
{
return x_53;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_53, 0);
lean_inc(x_89);
lean_dec(x_53);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
block_212:
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
x_105 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
x_106 = lean_int_dec_eq(x_104, x_105);
lean_dec(x_104);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec_ref(x_93);
lean_dec(x_14);
lean_dec_ref(x_11);
x_107 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_94, x_95, x_96, x_97);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = lean_box(0);
x_110 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6;
x_111 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_112 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__7;
lean_inc_ref(x_4);
x_113 = l_Lean_Name_mkStr3(x_4, x_111, x_112);
x_114 = l_Lean_mkConst(x_113, x_109);
x_115 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_116 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_117 = lean_int_dec_le(x_105, x_103);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_118 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__13;
lean_inc_ref(x_4);
x_119 = l_Lean_Name_mkStr1(x_4);
x_120 = l_Lean_Expr_const___override(x_119, x_109);
x_121 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
x_122 = l_Lean_Name_mkStr2(x_4, x_121);
x_123 = l_Lean_Expr_const___override(x_122, x_109);
x_124 = lean_int_neg(x_103);
lean_dec(x_103);
x_125 = l_Int_toNat(x_124);
lean_dec(x_124);
x_126 = l_Lean_instToExprInt_mkNat(x_125);
x_127 = l_Lean_mkApp3(x_118, x_120, x_123, x_126);
x_19 = x_114;
x_20 = lean_box(0);
x_21 = x_110;
x_22 = x_115;
x_23 = x_116;
x_24 = x_108;
x_25 = x_127;
goto block_33;
}
else
{
lean_object* x_128; lean_object* x_129; 
lean_dec_ref(x_4);
x_128 = l_Int_toNat(x_103);
lean_dec(x_103);
x_129 = l_Lean_instToExprInt_mkNat(x_128);
x_19 = x_114;
x_20 = lean_box(0);
x_21 = x_110;
x_22 = x_115;
x_23 = x_116;
x_24 = x_108;
x_25 = x_129;
goto block_33;
}
}
else
{
uint8_t x_130; 
lean_dec(x_103);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_130 = !lean_is_exclusive(x_107);
if (x_130 == 0)
{
return x_107;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_107, 0);
lean_inc(x_131);
lean_dec(x_107);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_17);
x_133 = l_Int_Linear_Poly_div(x_103, x_93);
lean_inc_ref(x_133);
x_134 = l_Int_Linear_Poly_denoteExpr___redArg(x_11, x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
x_136 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_94, x_95, x_96, x_97);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec_ref(x_136);
x_138 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__15;
x_139 = l_Lean_mkIntEq(x_135, x_138);
x_140 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_141 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__16;
lean_inc_ref(x_4);
x_142 = l_Lean_Name_mkStr3(x_4, x_140, x_141);
x_143 = lean_box(0);
x_144 = l_Lean_mkConst(x_142, x_143);
x_145 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_146 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_147 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_133);
x_148 = lean_int_dec_le(x_105, x_103);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_149 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__13;
lean_inc_ref(x_4);
x_150 = l_Lean_Name_mkStr1(x_4);
x_151 = l_Lean_Expr_const___override(x_150, x_143);
x_152 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
x_153 = l_Lean_Name_mkStr2(x_4, x_152);
x_154 = l_Lean_Expr_const___override(x_153, x_143);
x_155 = lean_int_neg(x_103);
lean_dec(x_103);
x_156 = l_Int_toNat(x_155);
lean_dec(x_155);
x_157 = l_Lean_instToExprInt_mkNat(x_156);
x_158 = l_Lean_mkApp3(x_149, x_151, x_154, x_157);
x_34 = x_145;
x_35 = x_137;
x_36 = lean_box(0);
x_37 = x_146;
x_38 = x_139;
x_39 = x_144;
x_40 = x_147;
x_41 = x_158;
goto block_49;
}
else
{
lean_object* x_159; lean_object* x_160; 
lean_dec_ref(x_4);
x_159 = l_Int_toNat(x_103);
lean_dec(x_103);
x_160 = l_Lean_instToExprInt_mkNat(x_159);
x_34 = x_145;
x_35 = x_137;
x_36 = lean_box(0);
x_37 = x_146;
x_38 = x_139;
x_39 = x_144;
x_40 = x_147;
x_41 = x_160;
goto block_49;
}
}
else
{
uint8_t x_161; 
lean_dec(x_135);
lean_dec_ref(x_133);
lean_dec(x_103);
lean_dec_ref(x_18);
lean_dec(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_161 = !lean_is_exclusive(x_136);
if (x_161 == 0)
{
return x_136;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_136, 0);
lean_inc(x_162);
lean_dec(x_136);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
return x_163;
}
}
}
else
{
uint8_t x_164; 
lean_dec_ref(x_133);
lean_dec(x_103);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec_ref(x_18);
lean_dec(x_14);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_164 = !lean_is_exclusive(x_134);
if (x_164 == 0)
{
return x_134;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_134, 0);
lean_inc(x_165);
lean_dec(x_134);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_165);
return x_166;
}
}
}
}
else
{
lean_object* x_167; 
lean_dec(x_99);
lean_dec(x_17);
lean_dec(x_14);
lean_inc_ref(x_93);
x_167 = l_Int_Linear_Poly_denoteExpr___redArg(x_11, x_93);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
lean_dec_ref(x_167);
x_169 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_94, x_95, x_96, x_97);
if (lean_obj_tag(x_169) == 0)
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_171 = lean_ctor_get(x_169, 0);
x_172 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__15;
x_173 = l_Lean_mkIntEq(x_168, x_172);
x_174 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_175 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__17;
x_176 = l_Lean_Name_mkStr3(x_4, x_174, x_175);
x_177 = lean_box(0);
x_178 = l_Lean_mkConst(x_176, x_177);
x_179 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_180 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_181 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_93);
x_182 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_183 = l_Lean_mkApp5(x_178, x_171, x_179, x_180, x_181, x_182);
lean_inc_ref(x_173);
x_184 = l_Lean_mkPropEq(x_18, x_173);
x_185 = l_Lean_Meta_mkExpectedPropHint(x_183, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_173);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_169, 0, x_187);
return x_169;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_188 = lean_ctor_get(x_169, 0);
lean_inc(x_188);
lean_dec(x_169);
x_189 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__15;
x_190 = l_Lean_mkIntEq(x_168, x_189);
x_191 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_192 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__17;
x_193 = l_Lean_Name_mkStr3(x_4, x_191, x_192);
x_194 = lean_box(0);
x_195 = l_Lean_mkConst(x_193, x_194);
x_196 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_197 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_198 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_93);
x_199 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_200 = l_Lean_mkApp5(x_195, x_188, x_196, x_197, x_198, x_199);
lean_inc_ref(x_190);
x_201 = l_Lean_mkPropEq(x_18, x_190);
x_202 = l_Lean_Meta_mkExpectedPropHint(x_200, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_190);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_204);
return x_205;
}
}
else
{
uint8_t x_206; 
lean_dec(x_168);
lean_dec_ref(x_93);
lean_dec_ref(x_18);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_206 = !lean_is_exclusive(x_169);
if (x_206 == 0)
{
return x_169;
}
else
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_169, 0);
lean_inc(x_207);
lean_dec(x_169);
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_207);
return x_208;
}
}
}
else
{
uint8_t x_209; 
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec_ref(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_209 = !lean_is_exclusive(x_167);
if (x_209 == 0)
{
return x_167;
}
else
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_167, 0);
lean_inc(x_210);
lean_dec(x_167);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_210);
return x_211;
}
}
}
}
block_318:
{
if (x_213 == 0)
{
if (lean_obj_tag(x_93) == 0)
{
lean_dec_ref(x_1);
x_94 = x_6;
x_95 = x_7;
x_96 = x_8;
x_97 = x_9;
x_98 = lean_box(0);
goto block_212;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_93, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_93, 1);
lean_inc(x_215);
x_216 = lean_ctor_get(x_93, 2);
lean_inc_ref(x_216);
x_217 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__18;
x_218 = lean_int_dec_eq(x_214, x_217);
lean_dec(x_214);
if (x_218 == 0)
{
lean_dec_ref(x_216);
lean_dec(x_215);
lean_dec_ref(x_1);
x_94 = x_6;
x_95 = x_7;
x_96 = x_8;
x_97 = x_9;
x_98 = lean_box(0);
goto block_212;
}
else
{
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
lean_dec_ref(x_93);
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_11);
x_219 = lean_ctor_get(x_216, 0);
lean_inc(x_219);
lean_dec_ref(x_216);
x_220 = lean_array_get_borrowed(x_1, x_5, x_215);
x_221 = lean_int_neg(x_219);
lean_dec(x_219);
x_222 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
x_223 = lean_int_dec_le(x_222, x_221);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_224 = lean_box(0);
x_225 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__13;
lean_inc_ref(x_4);
x_226 = l_Lean_Name_mkStr1(x_4);
x_227 = l_Lean_Expr_const___override(x_226, x_224);
x_228 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
lean_inc_ref(x_4);
x_229 = l_Lean_Name_mkStr2(x_4, x_228);
x_230 = l_Lean_Expr_const___override(x_229, x_224);
x_231 = lean_int_neg(x_221);
lean_dec(x_221);
x_232 = l_Int_toNat(x_231);
lean_dec(x_231);
x_233 = l_Lean_instToExprInt_mkNat(x_232);
x_234 = l_Lean_mkApp3(x_225, x_227, x_230, x_233);
lean_inc_ref(x_220);
x_50 = x_220;
x_51 = x_215;
x_52 = x_234;
goto block_91;
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = l_Int_toNat(x_221);
lean_dec(x_221);
x_236 = l_Lean_instToExprInt_mkNat(x_235);
lean_inc_ref(x_220);
x_50 = x_220;
x_51 = x_215;
x_52 = x_236;
goto block_91;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_237 = lean_ctor_get(x_216, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_216, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_216, 2);
lean_inc_ref(x_239);
lean_dec_ref(x_216);
x_240 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__19;
x_241 = lean_int_dec_eq(x_237, x_240);
lean_dec(x_237);
if (x_241 == 0)
{
lean_dec_ref(x_239);
lean_dec(x_238);
lean_dec(x_215);
lean_dec_ref(x_1);
x_94 = x_6;
x_95 = x_7;
x_96 = x_8;
x_97 = x_9;
x_98 = lean_box(0);
goto block_212;
}
else
{
if (lean_obj_tag(x_239) == 0)
{
uint8_t x_242; 
x_242 = !lean_is_exclusive(x_239);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_243 = lean_ctor_get(x_239, 0);
x_244 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
x_245 = lean_int_dec_eq(x_243, x_244);
lean_dec(x_243);
if (x_245 == 0)
{
lean_free_object(x_239);
lean_dec(x_238);
lean_dec(x_215);
lean_dec_ref(x_1);
x_94 = x_6;
x_95 = x_7;
x_96 = x_8;
x_97 = x_9;
x_98 = lean_box(0);
goto block_212;
}
else
{
lean_object* x_246; 
lean_dec_ref(x_93);
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_inc_ref(x_5);
x_246 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_246) == 0)
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_246);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_248 = lean_ctor_get(x_246, 0);
lean_inc_ref(x_1);
x_249 = lean_array_get(x_1, x_5, x_215);
x_250 = lean_array_get(x_1, x_5, x_238);
lean_dec_ref(x_5);
x_251 = l_Lean_mkIntEq(x_249, x_250);
x_252 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_253 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__20;
x_254 = l_Lean_Name_mkStr3(x_4, x_252, x_253);
x_255 = lean_box(0);
x_256 = l_Lean_mkConst(x_254, x_255);
x_257 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_258 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_259 = l_Lean_mkNatLit(x_215);
x_260 = l_Lean_mkNatLit(x_238);
x_261 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_262 = l_Lean_mkApp6(x_256, x_248, x_257, x_258, x_259, x_260, x_261);
lean_inc_ref(x_251);
x_263 = l_Lean_mkPropEq(x_18, x_251);
x_264 = l_Lean_Meta_mkExpectedPropHint(x_262, x_263);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_251);
lean_ctor_set(x_265, 1, x_264);
lean_ctor_set_tag(x_239, 1);
lean_ctor_set(x_239, 0, x_265);
lean_ctor_set(x_246, 0, x_239);
return x_246;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_266 = lean_ctor_get(x_246, 0);
lean_inc(x_266);
lean_dec(x_246);
lean_inc_ref(x_1);
x_267 = lean_array_get(x_1, x_5, x_215);
x_268 = lean_array_get(x_1, x_5, x_238);
lean_dec_ref(x_5);
x_269 = l_Lean_mkIntEq(x_267, x_268);
x_270 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_271 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__20;
x_272 = l_Lean_Name_mkStr3(x_4, x_270, x_271);
x_273 = lean_box(0);
x_274 = l_Lean_mkConst(x_272, x_273);
x_275 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_276 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_277 = l_Lean_mkNatLit(x_215);
x_278 = l_Lean_mkNatLit(x_238);
x_279 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_280 = l_Lean_mkApp6(x_274, x_266, x_275, x_276, x_277, x_278, x_279);
lean_inc_ref(x_269);
x_281 = l_Lean_mkPropEq(x_18, x_269);
x_282 = l_Lean_Meta_mkExpectedPropHint(x_280, x_281);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_269);
lean_ctor_set(x_283, 1, x_282);
lean_ctor_set_tag(x_239, 1);
lean_ctor_set(x_239, 0, x_283);
x_284 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_284, 0, x_239);
return x_284;
}
}
else
{
uint8_t x_285; 
lean_free_object(x_239);
lean_dec(x_238);
lean_dec(x_215);
lean_dec_ref(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_285 = !lean_is_exclusive(x_246);
if (x_285 == 0)
{
return x_246;
}
else
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_246, 0);
lean_inc(x_286);
lean_dec(x_246);
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_286);
return x_287;
}
}
}
}
else
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_288 = lean_ctor_get(x_239, 0);
lean_inc(x_288);
lean_dec(x_239);
x_289 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
x_290 = lean_int_dec_eq(x_288, x_289);
lean_dec(x_288);
if (x_290 == 0)
{
lean_dec(x_238);
lean_dec(x_215);
lean_dec_ref(x_1);
x_94 = x_6;
x_95 = x_7;
x_96 = x_8;
x_97 = x_9;
x_98 = lean_box(0);
goto block_212;
}
else
{
lean_object* x_291; 
lean_dec_ref(x_93);
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_inc_ref(x_5);
x_291 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_293 = x_291;
} else {
 lean_dec_ref(x_291);
 x_293 = lean_box(0);
}
lean_inc_ref(x_1);
x_294 = lean_array_get(x_1, x_5, x_215);
x_295 = lean_array_get(x_1, x_5, x_238);
lean_dec_ref(x_5);
x_296 = l_Lean_mkIntEq(x_294, x_295);
x_297 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_298 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__20;
x_299 = l_Lean_Name_mkStr3(x_4, x_297, x_298);
x_300 = lean_box(0);
x_301 = l_Lean_mkConst(x_299, x_300);
x_302 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_303 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_304 = l_Lean_mkNatLit(x_215);
x_305 = l_Lean_mkNatLit(x_238);
x_306 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_307 = l_Lean_mkApp6(x_301, x_292, x_302, x_303, x_304, x_305, x_306);
lean_inc_ref(x_296);
x_308 = l_Lean_mkPropEq(x_18, x_296);
x_309 = l_Lean_Meta_mkExpectedPropHint(x_307, x_308);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_296);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_311, 0, x_310);
if (lean_is_scalar(x_293)) {
 x_312 = lean_alloc_ctor(0, 1, 0);
} else {
 x_312 = x_293;
}
lean_ctor_set(x_312, 0, x_311);
return x_312;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_238);
lean_dec(x_215);
lean_dec_ref(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_313 = lean_ctor_get(x_291, 0);
lean_inc(x_313);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_314 = x_291;
} else {
 lean_dec_ref(x_291);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(1, 1, 0);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_313);
return x_315;
}
}
}
}
else
{
lean_dec_ref(x_239);
lean_dec(x_238);
lean_dec(x_215);
lean_dec_ref(x_1);
x_94 = x_6;
x_95 = x_7;
x_96 = x_8;
x_97 = x_9;
x_98 = lean_box(0);
goto block_212;
}
}
}
}
}
}
else
{
lean_object* x_316; lean_object* x_317; 
lean_dec_ref(x_93);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_316 = lean_box(0);
x_317 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_317, 0, x_316);
return x_317;
}
}
}
else
{
uint8_t x_397; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_397 = !lean_is_exclusive(x_15);
if (x_397 == 0)
{
return x_15;
}
else
{
lean_object* x_398; lean_object* x_399; 
x_398 = lean_ctor_get(x_15, 0);
lean_inc(x_398);
lean_dec(x_15);
x_399 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_399, 0, x_398);
return x_399;
}
}
}
else
{
uint8_t x_400; 
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_400 = !lean_is_exclusive(x_12);
if (x_400 == 0)
{
return x_12;
}
else
{
lean_object* x_401; lean_object* x_402; 
x_401 = lean_ctor_get(x_12, 0);
lean_inc(x_401);
lean_dec(x_12);
x_402 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_402, 0, x_401);
return x_402;
}
}
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
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
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = lean_box(0);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_7);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_instInhabitedExpr;
x_17 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___boxed), 10, 4);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_13);
lean_closure_set(x_18, 2, x_14);
lean_closure_set(x_18, 3, x_17);
x_19 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_20 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_15, x_19, x_18, x_2, x_3, x_4, x_5);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec(x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lean_instInhabitedExpr;
x_30 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___boxed), 10, 4);
lean_closure_set(x_31, 0, x_29);
lean_closure_set(x_31, 1, x_26);
lean_closure_set(x_31, 2, x_27);
lean_closure_set(x_31, 3, x_30);
x_32 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_33 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_28, x_32, x_31, x_2, x_3, x_4, x_5);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_34 = !lean_is_exclusive(x_7);
if (x_34 == 0)
{
return x_7;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_7, 0);
lean_inc(x_35);
lean_dec(x_7);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_le_coeff", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_le_coeff_tight", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_le", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_eq_true", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le_eq_false", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_6);
lean_inc_ref(x_2);
lean_inc_ref(x_12);
x_13 = l_Int_Linear_Expr_denoteExpr___redArg(x_12, x_2);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_3);
lean_inc_ref(x_12);
x_16 = l_Int_Linear_Expr_denoteExpr___redArg(x_12, x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_180; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_18 = x_16;
} else {
 lean_dec_ref(x_16);
 x_18 = lean_box(0);
}
x_19 = l_Lean_mkIntLE(x_15, x_17);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_51 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_3);
x_52 = l_Int_Linear_Expr_norm(x_51);
lean_dec_ref(x_51);
x_180 = l_Int_Linear_Poly_isUnsatLe(x_52);
if (x_180 == 0)
{
uint8_t x_181; 
x_181 = l_Int_Linear_Poly_isValidLe(x_52);
if (x_181 == 0)
{
if (x_5 == 0)
{
lean_free_object(x_13);
goto block_179;
}
else
{
lean_object* x_182; uint8_t x_183; 
lean_inc_ref(x_52);
x_182 = l_Int_Linear_Poly_toExpr(x_52);
x_183 = l_Int_Linear_instBEqExpr_beq(x_182, x_2);
lean_dec_ref(x_182);
if (x_183 == 0)
{
lean_free_object(x_13);
goto block_179;
}
else
{
lean_object* x_184; uint8_t x_185; 
x_184 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__21;
x_185 = l_Int_Linear_instBEqExpr_beq(x_3, x_184);
if (x_185 == 0)
{
lean_free_object(x_13);
goto block_179;
}
else
{
lean_object* x_186; 
lean_dec_ref(x_52);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_186 = lean_box(0);
lean_ctor_set(x_13, 0, x_186);
return x_13;
}
}
}
}
else
{
lean_object* x_187; 
lean_dec_ref(x_52);
lean_dec(x_18);
lean_free_object(x_13);
lean_dec_ref(x_12);
x_187 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_187) == 0)
{
uint8_t x_188; 
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_189 = lean_ctor_get(x_187, 0);
x_190 = lean_box(0);
x_191 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__24;
x_192 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_193 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__3;
x_194 = l_Lean_Name_mkStr3(x_4, x_192, x_193);
x_195 = l_Lean_mkConst(x_194, x_190);
x_196 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_197 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_198 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_199 = l_Lean_mkApp4(x_195, x_189, x_196, x_197, x_198);
x_200 = l_Lean_mkPropEq(x_19, x_191);
x_201 = l_Lean_Meta_mkExpectedPropHint(x_199, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_191);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_187, 0, x_203);
return x_187;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_204 = lean_ctor_get(x_187, 0);
lean_inc(x_204);
lean_dec(x_187);
x_205 = lean_box(0);
x_206 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__24;
x_207 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_208 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__3;
x_209 = l_Lean_Name_mkStr3(x_4, x_207, x_208);
x_210 = l_Lean_mkConst(x_209, x_205);
x_211 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_212 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_213 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_214 = l_Lean_mkApp4(x_210, x_204, x_211, x_212, x_213);
x_215 = l_Lean_mkPropEq(x_19, x_206);
x_216 = l_Lean_Meta_mkExpectedPropHint(x_214, x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_206);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_217);
x_219 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_219, 0, x_218);
return x_219;
}
}
else
{
uint8_t x_220; 
lean_dec_ref(x_19);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_220 = !lean_is_exclusive(x_187);
if (x_220 == 0)
{
return x_187;
}
else
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_187, 0);
lean_inc(x_221);
lean_dec(x_187);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_221);
return x_222;
}
}
}
}
else
{
lean_object* x_223; 
lean_dec_ref(x_52);
lean_dec(x_18);
lean_free_object(x_13);
lean_dec_ref(x_12);
x_223 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_223) == 0)
{
uint8_t x_224; 
x_224 = !lean_is_exclusive(x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_225 = lean_ctor_get(x_223, 0);
x_226 = lean_box(0);
x_227 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6;
x_228 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_229 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__4;
x_230 = l_Lean_Name_mkStr3(x_4, x_228, x_229);
x_231 = l_Lean_mkConst(x_230, x_226);
x_232 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_233 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_234 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_235 = l_Lean_mkApp4(x_231, x_225, x_232, x_233, x_234);
x_236 = l_Lean_mkPropEq(x_19, x_227);
x_237 = l_Lean_Meta_mkExpectedPropHint(x_235, x_236);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_227);
lean_ctor_set(x_238, 1, x_237);
x_239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_223, 0, x_239);
return x_223;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_240 = lean_ctor_get(x_223, 0);
lean_inc(x_240);
lean_dec(x_223);
x_241 = lean_box(0);
x_242 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6;
x_243 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_244 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__4;
x_245 = l_Lean_Name_mkStr3(x_4, x_243, x_244);
x_246 = l_Lean_mkConst(x_245, x_241);
x_247 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_248 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_249 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_250 = l_Lean_mkApp4(x_246, x_240, x_247, x_248, x_249);
x_251 = l_Lean_mkPropEq(x_19, x_242);
x_252 = l_Lean_Meta_mkExpectedPropHint(x_250, x_251);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_242);
lean_ctor_set(x_253, 1, x_252);
x_254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_254, 0, x_253);
x_255 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_255, 0, x_254);
return x_255;
}
}
else
{
uint8_t x_256; 
lean_dec_ref(x_19);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_256 = !lean_is_exclusive(x_223);
if (x_256 == 0)
{
return x_223;
}
else
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_223, 0);
lean_inc(x_257);
lean_dec(x_223);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_257);
return x_258;
}
}
}
block_28:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc_ref(x_20);
x_23 = l_Lean_mkPropEq(x_19, x_20);
x_24 = l_Lean_Meta_mkExpectedPropHint(x_21, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
if (lean_is_scalar(x_18)) {
 x_27 = lean_alloc_ctor(0, 1, 0);
} else {
 x_27 = x_18;
}
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_38 = l_Lean_mkApp6(x_29, x_35, x_32, x_33, x_30, x_36, x_37);
x_20 = x_34;
x_21 = x_38;
x_22 = lean_box(0);
goto block_28;
}
block_50:
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_49 = l_Lean_mkApp6(x_42, x_40, x_45, x_43, x_41, x_47, x_48);
x_20 = x_46;
x_21 = x_49;
x_22 = lean_box(0);
goto block_28;
}
block_123:
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Int_Linear_Poly_div(x_55, x_52);
lean_inc_ref(x_57);
x_58 = l_Int_Linear_Poly_denoteExpr___redArg(x_12, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = l_Lean_mkIntLit(x_53);
x_61 = l_Lean_mkIntLE(x_59, x_60);
if (x_56 == 0)
{
lean_object* x_62; 
x_62 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_65 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__0;
lean_inc_ref(x_4);
x_66 = l_Lean_Name_mkStr3(x_4, x_64, x_65);
x_67 = lean_box(0);
x_68 = l_Lean_mkConst(x_66, x_67);
x_69 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_70 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_71 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_57);
x_72 = lean_int_dec_le(x_53, x_55);
lean_dec(x_53);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_73 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10;
x_74 = l_Lean_Level_ofNat(x_54);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_67);
x_76 = l_Lean_Expr_const___override(x_73, x_75);
lean_inc_ref(x_4);
x_77 = l_Lean_Name_mkStr1(x_4);
x_78 = l_Lean_Expr_const___override(x_77, x_67);
x_79 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
x_80 = l_Lean_Name_mkStr2(x_4, x_79);
x_81 = l_Lean_Expr_const___override(x_80, x_67);
x_82 = lean_int_neg(x_55);
lean_dec(x_55);
x_83 = l_Int_toNat(x_82);
lean_dec(x_82);
x_84 = l_Lean_instToExprInt_mkNat(x_83);
x_85 = l_Lean_mkApp3(x_76, x_78, x_81, x_84);
x_29 = x_68;
x_30 = x_71;
x_31 = lean_box(0);
x_32 = x_69;
x_33 = x_70;
x_34 = x_61;
x_35 = x_63;
x_36 = x_85;
goto block_39;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec_ref(x_4);
x_86 = l_Int_toNat(x_55);
lean_dec(x_55);
x_87 = l_Lean_instToExprInt_mkNat(x_86);
x_29 = x_68;
x_30 = x_71;
x_31 = lean_box(0);
x_32 = x_69;
x_33 = x_70;
x_34 = x_61;
x_35 = x_63;
x_36 = x_87;
goto block_39;
}
}
else
{
uint8_t x_88; 
lean_dec_ref(x_61);
lean_dec_ref(x_57);
lean_dec(x_55);
lean_dec(x_53);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_88 = !lean_is_exclusive(x_62);
if (x_88 == 0)
{
return x_62;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_62, 0);
lean_inc(x_89);
lean_dec(x_62);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; 
x_91 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
x_93 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_94 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__1;
lean_inc_ref(x_4);
x_95 = l_Lean_Name_mkStr3(x_4, x_93, x_94);
x_96 = lean_box(0);
x_97 = l_Lean_mkConst(x_95, x_96);
x_98 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_99 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_100 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_57);
x_101 = lean_int_dec_le(x_53, x_55);
lean_dec(x_53);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_102 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10;
x_103 = l_Lean_Level_ofNat(x_54);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_96);
x_105 = l_Lean_Expr_const___override(x_102, x_104);
lean_inc_ref(x_4);
x_106 = l_Lean_Name_mkStr1(x_4);
x_107 = l_Lean_Expr_const___override(x_106, x_96);
x_108 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
x_109 = l_Lean_Name_mkStr2(x_4, x_108);
x_110 = l_Lean_Expr_const___override(x_109, x_96);
x_111 = lean_int_neg(x_55);
lean_dec(x_55);
x_112 = l_Int_toNat(x_111);
lean_dec(x_111);
x_113 = l_Lean_instToExprInt_mkNat(x_112);
x_114 = l_Lean_mkApp3(x_105, x_107, x_110, x_113);
x_40 = x_92;
x_41 = x_100;
x_42 = x_97;
x_43 = x_99;
x_44 = lean_box(0);
x_45 = x_98;
x_46 = x_61;
x_47 = x_114;
goto block_50;
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec_ref(x_4);
x_115 = l_Int_toNat(x_55);
lean_dec(x_55);
x_116 = l_Lean_instToExprInt_mkNat(x_115);
x_40 = x_92;
x_41 = x_100;
x_42 = x_97;
x_43 = x_99;
x_44 = lean_box(0);
x_45 = x_98;
x_46 = x_61;
x_47 = x_116;
goto block_50;
}
}
else
{
uint8_t x_117; 
lean_dec_ref(x_61);
lean_dec_ref(x_57);
lean_dec(x_55);
lean_dec(x_53);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_117 = !lean_is_exclusive(x_91);
if (x_117 == 0)
{
return x_91;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_91, 0);
lean_inc(x_118);
lean_dec(x_91);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
}
}
else
{
uint8_t x_120; 
lean_dec_ref(x_57);
lean_dec(x_55);
lean_dec(x_53);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_120 = !lean_is_exclusive(x_58);
if (x_120 == 0)
{
return x_58;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_58, 0);
lean_inc(x_121);
lean_dec(x_58);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
}
block_179:
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_124 = l_Int_Linear_Poly_gcdCoeffs_x27(x_52);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_dec_eq(x_124, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_127 = l_Int_Linear_Poly_getConst(x_52);
x_128 = lean_nat_to_int(x_124);
x_129 = lean_int_emod(x_127, x_128);
lean_dec(x_127);
x_130 = lean_unsigned_to_nat(0u);
x_131 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
x_132 = lean_int_dec_eq(x_129, x_131);
lean_dec(x_129);
if (x_132 == 0)
{
uint8_t x_133; 
x_133 = 1;
x_53 = x_131;
x_54 = x_130;
x_55 = x_128;
x_56 = x_133;
goto block_123;
}
else
{
x_53 = x_131;
x_54 = x_130;
x_55 = x_128;
x_56 = x_126;
goto block_123;
}
}
else
{
lean_object* x_134; 
lean_dec(x_124);
lean_dec(x_18);
lean_inc_ref(x_52);
x_134 = l_Int_Linear_Poly_denoteExpr___redArg(x_12, x_52);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
x_136 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__15;
x_140 = l_Lean_mkIntLE(x_135, x_139);
x_141 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_142 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__2;
x_143 = l_Lean_Name_mkStr3(x_4, x_141, x_142);
x_144 = lean_box(0);
x_145 = l_Lean_mkConst(x_143, x_144);
x_146 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_147 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_148 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_52);
x_149 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_150 = l_Lean_mkApp5(x_145, x_138, x_146, x_147, x_148, x_149);
lean_inc_ref(x_140);
x_151 = l_Lean_mkPropEq(x_19, x_140);
x_152 = l_Lean_Meta_mkExpectedPropHint(x_150, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_140);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_136, 0, x_154);
return x_136;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_155 = lean_ctor_get(x_136, 0);
lean_inc(x_155);
lean_dec(x_136);
x_156 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__15;
x_157 = l_Lean_mkIntLE(x_135, x_156);
x_158 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_159 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__2;
x_160 = l_Lean_Name_mkStr3(x_4, x_158, x_159);
x_161 = lean_box(0);
x_162 = l_Lean_mkConst(x_160, x_161);
x_163 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_164 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_165 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_52);
x_166 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_167 = l_Lean_mkApp5(x_162, x_155, x_163, x_164, x_165, x_166);
lean_inc_ref(x_157);
x_168 = l_Lean_mkPropEq(x_19, x_157);
x_169 = l_Lean_Meta_mkExpectedPropHint(x_167, x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_157);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_170);
x_172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_172, 0, x_171);
return x_172;
}
}
else
{
uint8_t x_173; 
lean_dec(x_135);
lean_dec_ref(x_52);
lean_dec_ref(x_19);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_173 = !lean_is_exclusive(x_136);
if (x_173 == 0)
{
return x_136;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_136, 0);
lean_inc(x_174);
lean_dec(x_136);
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_174);
return x_175;
}
}
}
else
{
uint8_t x_176; 
lean_dec_ref(x_52);
lean_dec_ref(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_176 = !lean_is_exclusive(x_134);
if (x_176 == 0)
{
return x_134;
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_134, 0);
lean_inc(x_177);
lean_dec(x_134);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
return x_178;
}
}
}
}
}
else
{
uint8_t x_259; 
lean_free_object(x_13);
lean_dec(x_15);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_259 = !lean_is_exclusive(x_16);
if (x_259 == 0)
{
return x_16;
}
else
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_16, 0);
lean_inc(x_260);
lean_dec(x_16);
x_261 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_261, 0, x_260);
return x_261;
}
}
}
else
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_13, 0);
lean_inc(x_262);
lean_dec(x_13);
lean_inc_ref(x_3);
lean_inc_ref(x_12);
x_263 = l_Int_Linear_Expr_denoteExpr___redArg(x_12, x_3);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; uint8_t x_410; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 x_265 = x_263;
} else {
 lean_dec_ref(x_263);
 x_265 = lean_box(0);
}
x_266 = l_Lean_mkIntLE(x_262, x_264);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_298 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_298, 0, x_2);
lean_ctor_set(x_298, 1, x_3);
x_299 = l_Int_Linear_Expr_norm(x_298);
lean_dec_ref(x_298);
x_410 = l_Int_Linear_Poly_isUnsatLe(x_299);
if (x_410 == 0)
{
uint8_t x_411; 
x_411 = l_Int_Linear_Poly_isValidLe(x_299);
if (x_411 == 0)
{
if (x_5 == 0)
{
goto block_409;
}
else
{
lean_object* x_412; uint8_t x_413; 
lean_inc_ref(x_299);
x_412 = l_Int_Linear_Poly_toExpr(x_299);
x_413 = l_Int_Linear_instBEqExpr_beq(x_412, x_2);
lean_dec_ref(x_412);
if (x_413 == 0)
{
goto block_409;
}
else
{
lean_object* x_414; uint8_t x_415; 
x_414 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__21;
x_415 = l_Int_Linear_instBEqExpr_beq(x_3, x_414);
if (x_415 == 0)
{
goto block_409;
}
else
{
lean_object* x_416; lean_object* x_417; 
lean_dec_ref(x_299);
lean_dec_ref(x_266);
lean_dec(x_265);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_416 = lean_box(0);
x_417 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_417, 0, x_416);
return x_417;
}
}
}
}
else
{
lean_object* x_418; 
lean_dec_ref(x_299);
lean_dec(x_265);
lean_dec_ref(x_12);
x_418 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 x_420 = x_418;
} else {
 lean_dec_ref(x_418);
 x_420 = lean_box(0);
}
x_421 = lean_box(0);
x_422 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__24;
x_423 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_424 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__3;
x_425 = l_Lean_Name_mkStr3(x_4, x_423, x_424);
x_426 = l_Lean_mkConst(x_425, x_421);
x_427 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_428 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_429 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_430 = l_Lean_mkApp4(x_426, x_419, x_427, x_428, x_429);
x_431 = l_Lean_mkPropEq(x_266, x_422);
x_432 = l_Lean_Meta_mkExpectedPropHint(x_430, x_431);
x_433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_433, 0, x_422);
lean_ctor_set(x_433, 1, x_432);
x_434 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_434, 0, x_433);
if (lean_is_scalar(x_420)) {
 x_435 = lean_alloc_ctor(0, 1, 0);
} else {
 x_435 = x_420;
}
lean_ctor_set(x_435, 0, x_434);
return x_435;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_dec_ref(x_266);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_436 = lean_ctor_get(x_418, 0);
lean_inc(x_436);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 x_437 = x_418;
} else {
 lean_dec_ref(x_418);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(1, 1, 0);
} else {
 x_438 = x_437;
}
lean_ctor_set(x_438, 0, x_436);
return x_438;
}
}
}
else
{
lean_object* x_439; 
lean_dec_ref(x_299);
lean_dec(x_265);
lean_dec_ref(x_12);
x_439 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 x_441 = x_439;
} else {
 lean_dec_ref(x_439);
 x_441 = lean_box(0);
}
x_442 = lean_box(0);
x_443 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6;
x_444 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_445 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__4;
x_446 = l_Lean_Name_mkStr3(x_4, x_444, x_445);
x_447 = l_Lean_mkConst(x_446, x_442);
x_448 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_449 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_450 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_451 = l_Lean_mkApp4(x_447, x_440, x_448, x_449, x_450);
x_452 = l_Lean_mkPropEq(x_266, x_443);
x_453 = l_Lean_Meta_mkExpectedPropHint(x_451, x_452);
x_454 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_454, 0, x_443);
lean_ctor_set(x_454, 1, x_453);
x_455 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_455, 0, x_454);
if (lean_is_scalar(x_441)) {
 x_456 = lean_alloc_ctor(0, 1, 0);
} else {
 x_456 = x_441;
}
lean_ctor_set(x_456, 0, x_455);
return x_456;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec_ref(x_266);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_457 = lean_ctor_get(x_439, 0);
lean_inc(x_457);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 x_458 = x_439;
} else {
 lean_dec_ref(x_439);
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
block_275:
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_inc_ref(x_267);
x_270 = l_Lean_mkPropEq(x_266, x_267);
x_271 = l_Lean_Meta_mkExpectedPropHint(x_268, x_270);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_267);
lean_ctor_set(x_272, 1, x_271);
x_273 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_273, 0, x_272);
if (lean_is_scalar(x_265)) {
 x_274 = lean_alloc_ctor(0, 1, 0);
} else {
 x_274 = x_265;
}
lean_ctor_set(x_274, 0, x_273);
return x_274;
}
block_286:
{
lean_object* x_284; lean_object* x_285; 
x_284 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_285 = l_Lean_mkApp6(x_276, x_282, x_279, x_280, x_277, x_283, x_284);
x_267 = x_281;
x_268 = x_285;
x_269 = lean_box(0);
goto block_275;
}
block_297:
{
lean_object* x_295; lean_object* x_296; 
x_295 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_296 = l_Lean_mkApp6(x_289, x_287, x_292, x_290, x_288, x_294, x_295);
x_267 = x_293;
x_268 = x_296;
x_269 = lean_box(0);
goto block_275;
}
block_370:
{
lean_object* x_304; lean_object* x_305; 
x_304 = l_Int_Linear_Poly_div(x_302, x_299);
lean_inc_ref(x_304);
x_305 = l_Int_Linear_Poly_denoteExpr___redArg(x_12, x_304);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
lean_dec_ref(x_305);
x_307 = l_Lean_mkIntLit(x_300);
x_308 = l_Lean_mkIntLE(x_306, x_307);
if (x_303 == 0)
{
lean_object* x_309; 
x_309 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
lean_dec_ref(x_309);
x_311 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_312 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__0;
lean_inc_ref(x_4);
x_313 = l_Lean_Name_mkStr3(x_4, x_311, x_312);
x_314 = lean_box(0);
x_315 = l_Lean_mkConst(x_313, x_314);
x_316 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_317 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_318 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_304);
x_319 = lean_int_dec_le(x_300, x_302);
lean_dec(x_300);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_320 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10;
x_321 = l_Lean_Level_ofNat(x_301);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_314);
x_323 = l_Lean_Expr_const___override(x_320, x_322);
lean_inc_ref(x_4);
x_324 = l_Lean_Name_mkStr1(x_4);
x_325 = l_Lean_Expr_const___override(x_324, x_314);
x_326 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
x_327 = l_Lean_Name_mkStr2(x_4, x_326);
x_328 = l_Lean_Expr_const___override(x_327, x_314);
x_329 = lean_int_neg(x_302);
lean_dec(x_302);
x_330 = l_Int_toNat(x_329);
lean_dec(x_329);
x_331 = l_Lean_instToExprInt_mkNat(x_330);
x_332 = l_Lean_mkApp3(x_323, x_325, x_328, x_331);
x_276 = x_315;
x_277 = x_318;
x_278 = lean_box(0);
x_279 = x_316;
x_280 = x_317;
x_281 = x_308;
x_282 = x_310;
x_283 = x_332;
goto block_286;
}
else
{
lean_object* x_333; lean_object* x_334; 
lean_dec_ref(x_4);
x_333 = l_Int_toNat(x_302);
lean_dec(x_302);
x_334 = l_Lean_instToExprInt_mkNat(x_333);
x_276 = x_315;
x_277 = x_318;
x_278 = lean_box(0);
x_279 = x_316;
x_280 = x_317;
x_281 = x_308;
x_282 = x_310;
x_283 = x_334;
goto block_286;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec_ref(x_308);
lean_dec_ref(x_304);
lean_dec(x_302);
lean_dec(x_300);
lean_dec_ref(x_266);
lean_dec(x_265);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_335 = lean_ctor_get(x_309, 0);
lean_inc(x_335);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 x_336 = x_309;
} else {
 lean_dec_ref(x_309);
 x_336 = lean_box(0);
}
if (lean_is_scalar(x_336)) {
 x_337 = lean_alloc_ctor(1, 1, 0);
} else {
 x_337 = x_336;
}
lean_ctor_set(x_337, 0, x_335);
return x_337;
}
}
else
{
lean_object* x_338; 
x_338 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec_ref(x_338);
x_340 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_341 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__1;
lean_inc_ref(x_4);
x_342 = l_Lean_Name_mkStr3(x_4, x_340, x_341);
x_343 = lean_box(0);
x_344 = l_Lean_mkConst(x_342, x_343);
x_345 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_346 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_347 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_304);
x_348 = lean_int_dec_le(x_300, x_302);
lean_dec(x_300);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_349 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10;
x_350 = l_Lean_Level_ofNat(x_301);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_343);
x_352 = l_Lean_Expr_const___override(x_349, x_351);
lean_inc_ref(x_4);
x_353 = l_Lean_Name_mkStr1(x_4);
x_354 = l_Lean_Expr_const___override(x_353, x_343);
x_355 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
x_356 = l_Lean_Name_mkStr2(x_4, x_355);
x_357 = l_Lean_Expr_const___override(x_356, x_343);
x_358 = lean_int_neg(x_302);
lean_dec(x_302);
x_359 = l_Int_toNat(x_358);
lean_dec(x_358);
x_360 = l_Lean_instToExprInt_mkNat(x_359);
x_361 = l_Lean_mkApp3(x_352, x_354, x_357, x_360);
x_287 = x_339;
x_288 = x_347;
x_289 = x_344;
x_290 = x_346;
x_291 = lean_box(0);
x_292 = x_345;
x_293 = x_308;
x_294 = x_361;
goto block_297;
}
else
{
lean_object* x_362; lean_object* x_363; 
lean_dec_ref(x_4);
x_362 = l_Int_toNat(x_302);
lean_dec(x_302);
x_363 = l_Lean_instToExprInt_mkNat(x_362);
x_287 = x_339;
x_288 = x_347;
x_289 = x_344;
x_290 = x_346;
x_291 = lean_box(0);
x_292 = x_345;
x_293 = x_308;
x_294 = x_363;
goto block_297;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec_ref(x_308);
lean_dec_ref(x_304);
lean_dec(x_302);
lean_dec(x_300);
lean_dec_ref(x_266);
lean_dec(x_265);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_364 = lean_ctor_get(x_338, 0);
lean_inc(x_364);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 x_365 = x_338;
} else {
 lean_dec_ref(x_338);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 1, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_364);
return x_366;
}
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec_ref(x_304);
lean_dec(x_302);
lean_dec(x_300);
lean_dec_ref(x_266);
lean_dec(x_265);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_367 = lean_ctor_get(x_305, 0);
lean_inc(x_367);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 x_368 = x_305;
} else {
 lean_dec_ref(x_305);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(1, 1, 0);
} else {
 x_369 = x_368;
}
lean_ctor_set(x_369, 0, x_367);
return x_369;
}
}
block_409:
{
lean_object* x_371; lean_object* x_372; uint8_t x_373; 
x_371 = l_Int_Linear_Poly_gcdCoeffs_x27(x_299);
x_372 = lean_unsigned_to_nat(1u);
x_373 = lean_nat_dec_eq(x_371, x_372);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; 
x_374 = l_Int_Linear_Poly_getConst(x_299);
x_375 = lean_nat_to_int(x_371);
x_376 = lean_int_emod(x_374, x_375);
lean_dec(x_374);
x_377 = lean_unsigned_to_nat(0u);
x_378 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
x_379 = lean_int_dec_eq(x_376, x_378);
lean_dec(x_376);
if (x_379 == 0)
{
uint8_t x_380; 
x_380 = 1;
x_300 = x_378;
x_301 = x_377;
x_302 = x_375;
x_303 = x_380;
goto block_370;
}
else
{
x_300 = x_378;
x_301 = x_377;
x_302 = x_375;
x_303 = x_373;
goto block_370;
}
}
else
{
lean_object* x_381; 
lean_dec(x_371);
lean_dec(x_265);
lean_inc_ref(x_299);
x_381 = l_Int_Linear_Poly_denoteExpr___redArg(x_12, x_299);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
lean_dec_ref(x_381);
x_383 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 x_385 = x_383;
} else {
 lean_dec_ref(x_383);
 x_385 = lean_box(0);
}
x_386 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__15;
x_387 = l_Lean_mkIntLE(x_382, x_386);
x_388 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_389 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__2;
x_390 = l_Lean_Name_mkStr3(x_4, x_388, x_389);
x_391 = lean_box(0);
x_392 = l_Lean_mkConst(x_390, x_391);
x_393 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_394 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_395 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_299);
x_396 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_397 = l_Lean_mkApp5(x_392, x_384, x_393, x_394, x_395, x_396);
lean_inc_ref(x_387);
x_398 = l_Lean_mkPropEq(x_266, x_387);
x_399 = l_Lean_Meta_mkExpectedPropHint(x_397, x_398);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_387);
lean_ctor_set(x_400, 1, x_399);
x_401 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_401, 0, x_400);
if (lean_is_scalar(x_385)) {
 x_402 = lean_alloc_ctor(0, 1, 0);
} else {
 x_402 = x_385;
}
lean_ctor_set(x_402, 0, x_401);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_382);
lean_dec_ref(x_299);
lean_dec_ref(x_266);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_403 = lean_ctor_get(x_383, 0);
lean_inc(x_403);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 x_404 = x_383;
} else {
 lean_dec_ref(x_383);
 x_404 = lean_box(0);
}
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 1, 0);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_403);
return x_405;
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec_ref(x_299);
lean_dec_ref(x_266);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_406 = lean_ctor_get(x_381, 0);
lean_inc(x_406);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 x_407 = x_381;
} else {
 lean_dec_ref(x_381);
 x_407 = lean_box(0);
}
if (lean_is_scalar(x_407)) {
 x_408 = lean_alloc_ctor(1, 1, 0);
} else {
 x_408 = x_407;
}
lean_ctor_set(x_408, 0, x_406);
return x_408;
}
}
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_262);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_460 = lean_ctor_get(x_263, 0);
lean_inc(x_460);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 x_461 = x_263;
} else {
 lean_dec_ref(x_263);
 x_461 = lean_box(0);
}
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(1, 1, 0);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_460);
return x_462;
}
}
}
else
{
uint8_t x_463; 
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_463 = !lean_is_exclusive(x_13);
if (x_463 == 0)
{
return x_13;
}
else
{
lean_object* x_464; lean_object* x_465; 
x_464 = lean_ctor_get(x_13, 0);
lean_inc(x_464);
lean_dec(x_13);
x_465 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_465, 0, x_464);
return x_465;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_41; uint8_t x_42; 
x_8 = l_Lean_instInhabitedExpr;
x_41 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2;
x_42 = l_Lean_Expr_isAppOf(x_1, x_41);
if (x_42 == 0)
{
x_9 = x_42;
goto block_40;
}
else
{
x_9 = x_2;
goto block_40;
}
block_40:
{
lean_object* x_10; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_10 = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_10);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_20 = lean_box(x_9);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___boxed), 11, 5);
lean_closure_set(x_21, 0, x_8);
lean_closure_set(x_21, 1, x_16);
lean_closure_set(x_21, 2, x_17);
lean_closure_set(x_21, 3, x_19);
lean_closure_set(x_21, 4, x_20);
x_22 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_23 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_18, x_22, x_21, x_3, x_4, x_5, x_6);
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_10, 0);
lean_inc(x_24);
lean_dec(x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec_ref(x_24);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_33 = lean_box(x_9);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___boxed), 11, 5);
lean_closure_set(x_34, 0, x_8);
lean_closure_set(x_34, 1, x_29);
lean_closure_set(x_34, 2, x_30);
lean_closure_set(x_34, 3, x_32);
lean_closure_set(x_34, 4, x_33);
x_35 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_36 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_31, x_35, x_34, x_3, x_4, x_5, x_6);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_37 = !lean_is_exclusive(x_10);
if (x_37 == 0)
{
return x_10;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_10, 0);
lean_inc(x_38);
lean_dec(x_10);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
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
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trans", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__1;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_levelOne;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__4;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = 0;
lean_inc(x_13);
x_15 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_13, x_14, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_2, 0, x_18);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
uint8_t x_19; 
lean_free_object(x_2);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__5;
x_25 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__6;
lean_inc(x_22);
x_26 = l_Lean_mkApp6(x_24, x_25, x_1, x_13, x_22, x_3, x_23);
lean_ctor_set(x_20, 1, x_26);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__5;
x_30 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__6;
lean_inc(x_27);
x_31 = l_Lean_mkApp6(x_29, x_30, x_1, x_13, x_27, x_3, x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_17, 0, x_32);
return x_15;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__5;
x_38 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__6;
lean_inc(x_34);
x_39 = l_Lean_mkApp6(x_37, x_38, x_1, x_13, x_34, x_3, x_35);
if (lean_is_scalar(x_36)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_36;
}
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_15, 0, x_41);
return x_15;
}
}
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_15, 0);
lean_inc(x_42);
lean_dec(x_15);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_13);
lean_ctor_set(x_43, 1, x_3);
lean_ctor_set(x_2, 0, x_43);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_2);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_free_object(x_2);
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_46 = x_42;
} else {
 lean_dec_ref(x_42);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_49 = x_45;
} else {
 lean_dec_ref(x_45);
 x_49 = lean_box(0);
}
x_50 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__5;
x_51 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__6;
lean_inc(x_47);
x_52 = l_Lean_mkApp6(x_50, x_51, x_1, x_13, x_47, x_3, x_48);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_49;
}
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
if (lean_is_scalar(x_46)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_46;
}
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
lean_free_object(x_2);
lean_dec(x_13);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_15;
}
}
else
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_2, 0);
lean_inc(x_56);
lean_dec(x_2);
x_57 = 0;
lean_inc(x_56);
x_58 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_56, x_57, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_1);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_3);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 1, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_65 = x_59;
} else {
 lean_dec_ref(x_59);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_68 = x_64;
} else {
 lean_dec_ref(x_64);
 x_68 = lean_box(0);
}
x_69 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__5;
x_70 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__6;
lean_inc(x_66);
x_71 = l_Lean_mkApp6(x_69, x_70, x_1, x_56, x_66, x_3, x_67);
if (lean_is_scalar(x_68)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_68;
}
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_71);
if (lean_is_scalar(x_65)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_65;
}
lean_ctor_set(x_73, 0, x_72);
if (lean_is_scalar(x_60)) {
 x_74 = lean_alloc_ctor(0, 1, 0);
} else {
 x_74 = x_60;
}
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
else
{
lean_dec(x_56);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_58;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt", 2, 2);
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
x_1 = lean_mk_string_unchecked("GE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ge", 2, 2);
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__18;
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_le_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_ge_eq", 9, 9);
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
x_1 = lean_mk_string_unchecked("not_lt_eq", 9, 9);
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
x_1 = lean_mk_string_unchecked("not_gt_eq", 9, 9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1;
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_1, x_10, x_2, x_3, x_4, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_appArg_x21(x_1);
x_13 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_12, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_24; uint8_t x_25; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_box(0);
x_16 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4;
x_24 = l_Lean_Expr_cleanupAnnotations(x_14);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec_ref(x_24);
x_17 = x_2;
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
goto block_23;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_inc_ref(x_24);
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_17 = x_2;
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
goto block_23;
}
else
{
lean_object* x_28; uint8_t x_29; 
lean_inc_ref(x_26);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec_ref(x_28);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_17 = x_2;
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
goto block_23;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_dec_ref(x_30);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
x_17 = x_2;
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
goto block_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_32);
lean_dec_ref(x_24);
x_33 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_33);
lean_dec_ref(x_26);
x_34 = lean_ctor_get(x_30, 1);
lean_inc_ref(x_34);
x_35 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_36 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7;
x_37 = l_Lean_Expr_isConstOf(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10;
x_39 = l_Lean_Expr_isConstOf(x_35, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13;
x_41 = l_Lean_Expr_isConstOf(x_35, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2;
x_43 = l_Lean_Expr_isConstOf(x_35, x_42);
lean_dec_ref(x_35);
if (x_43 == 0)
{
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_32);
x_17 = x_2;
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
goto block_23;
}
else
{
lean_object* x_44; 
x_44 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_34, x_3);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = l_Lean_Expr_cleanupAnnotations(x_45);
x_47 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_48 = l_Lean_Expr_isConstOf(x_46, x_47);
lean_dec_ref(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_33);
lean_dec_ref(x_32);
x_49 = lean_box(0);
x_50 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_15, x_16, x_49, x_2, x_3, x_4, x_5);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14;
lean_inc_ref(x_32);
x_52 = l_Lean_mkIntAdd(x_32, x_51);
lean_inc_ref(x_33);
x_53 = l_Lean_mkIntLE(x_52, x_33);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17;
x_56 = l_Lean_mkAppB(x_55, x_33, x_32);
x_57 = lean_box(0);
x_58 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_54, x_56, x_57, x_2, x_3, x_4, x_5);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_59 = !lean_is_exclusive(x_44);
if (x_59 == 0)
{
return x_44;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_44, 0);
lean_inc(x_60);
lean_dec(x_44);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
else
{
lean_object* x_62; 
lean_dec_ref(x_35);
x_62 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_34, x_3);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = l_Lean_Expr_cleanupAnnotations(x_63);
x_65 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_66 = l_Lean_Expr_isConstOf(x_64, x_65);
lean_dec_ref(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_33);
lean_dec_ref(x_32);
x_67 = lean_box(0);
x_68 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_15, x_16, x_67, x_2, x_3, x_4, x_5);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14;
lean_inc_ref(x_33);
x_70 = l_Lean_mkIntAdd(x_33, x_69);
lean_inc_ref(x_32);
x_71 = l_Lean_mkIntLE(x_70, x_32);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20;
x_74 = l_Lean_mkAppB(x_73, x_33, x_32);
x_75 = lean_box(0);
x_76 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_72, x_74, x_75, x_2, x_3, x_4, x_5);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_77 = !lean_is_exclusive(x_62);
if (x_77 == 0)
{
return x_62;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_62, 0);
lean_inc(x_78);
lean_dec(x_62);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_80; 
lean_dec_ref(x_35);
x_80 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_34, x_3);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = l_Lean_Expr_cleanupAnnotations(x_81);
x_83 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_84 = l_Lean_Expr_isConstOf(x_82, x_83);
lean_dec_ref(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_33);
lean_dec_ref(x_32);
x_85 = lean_box(0);
x_86 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_15, x_16, x_85, x_2, x_3, x_4, x_5);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_inc_ref(x_33);
lean_inc_ref(x_32);
x_87 = l_Lean_mkIntLE(x_32, x_33);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23;
x_90 = l_Lean_mkAppB(x_89, x_33, x_32);
x_91 = lean_box(0);
x_92 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_88, x_90, x_91, x_2, x_3, x_4, x_5);
return x_92;
}
}
else
{
uint8_t x_93; 
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_93 = !lean_is_exclusive(x_80);
if (x_93 == 0)
{
return x_80;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_80, 0);
lean_inc(x_94);
lean_dec(x_80);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
}
else
{
lean_object* x_96; 
lean_dec_ref(x_35);
x_96 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_34, x_3);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
x_98 = l_Lean_Expr_cleanupAnnotations(x_97);
x_99 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_100 = l_Lean_Expr_isConstOf(x_98, x_99);
lean_dec_ref(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec_ref(x_33);
lean_dec_ref(x_32);
x_101 = lean_box(0);
x_102 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_15, x_16, x_101, x_2, x_3, x_4, x_5);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_inc_ref(x_32);
lean_inc_ref(x_33);
x_103 = l_Lean_mkIntLE(x_33, x_32);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26;
x_106 = l_Lean_mkAppB(x_105, x_33, x_32);
x_107 = lean_box(0);
x_108 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_104, x_106, x_107, x_2, x_3, x_4, x_5);
return x_108;
}
}
else
{
uint8_t x_109; 
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_109 = !lean_is_exclusive(x_96);
if (x_109 == 0)
{
return x_96;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_96, 0);
lean_inc(x_110);
lean_dec(x_96);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
}
}
}
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_15, x_16, x_21, x_17, x_18, x_19, x_20);
return x_22;
}
}
else
{
uint8_t x_112; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_112 = !lean_is_exclusive(x_13);
if (x_112 == 0)
{
return x_13;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_13, 0);
lean_inc(x_113);
lean_dec(x_13);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
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
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_dvd_gcd", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_dvd", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dvd_eq_false", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_89; lean_object* x_90; 
lean_inc_ref(x_7);
x_89 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_89, 0, x_1);
lean_closure_set(x_89, 1, x_7);
lean_inc_ref(x_2);
lean_inc_ref(x_89);
x_90 = l_Int_Linear_Expr_denoteExpr___redArg(x_89, x_2);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_163; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
x_163 = lean_int_dec_le(x_4, x_6);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_164 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10;
x_165 = l_Lean_Level_ofNat(x_5);
x_166 = lean_box(0);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_Expr_const___override(x_164, x_167);
lean_inc_ref(x_3);
x_169 = l_Lean_Name_mkStr1(x_3);
x_170 = l_Lean_Expr_const___override(x_169, x_166);
x_171 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
lean_inc_ref(x_3);
x_172 = l_Lean_Name_mkStr2(x_3, x_171);
x_173 = l_Lean_Expr_const___override(x_172, x_166);
x_174 = lean_int_neg(x_6);
x_175 = l_Int_toNat(x_174);
lean_dec(x_174);
x_176 = l_Lean_instToExprInt_mkNat(x_175);
x_177 = l_Lean_mkApp3(x_168, x_170, x_173, x_176);
x_93 = x_177;
goto block_162;
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = l_Int_toNat(x_6);
x_179 = l_Lean_instToExprInt_mkNat(x_178);
x_93 = x_179;
goto block_162;
}
block_162:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_inc_ref(x_93);
x_94 = l_Lean_mkIntDvd(x_93, x_91);
x_95 = l_Int_Linear_Expr_norm(x_2);
lean_inc(x_6);
x_96 = l_Int_Linear_Poly_gcdCoeffs(x_95, x_6);
x_97 = l_Int_Linear_Poly_getConst(x_95);
x_98 = lean_int_emod(x_97, x_96);
lean_dec(x_97);
x_99 = lean_int_dec_eq(x_98, x_4);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
lean_dec(x_96);
lean_dec_ref(x_95);
lean_dec(x_92);
lean_dec_ref(x_89);
lean_dec(x_6);
x_100 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_box(0);
x_104 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6;
x_105 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_106 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__2;
x_107 = l_Lean_Name_mkStr3(x_3, x_105, x_106);
x_108 = l_Lean_mkConst(x_107, x_103);
x_109 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_110 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_111 = l_Lean_mkApp4(x_108, x_102, x_93, x_109, x_110);
x_112 = l_Lean_mkPropEq(x_94, x_104);
x_113 = l_Lean_Meta_mkExpectedPropHint(x_111, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_104);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_100, 0, x_115);
return x_100;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_116 = lean_ctor_get(x_100, 0);
lean_inc(x_116);
lean_dec(x_100);
x_117 = lean_box(0);
x_118 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6;
x_119 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_120 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__2;
x_121 = l_Lean_Name_mkStr3(x_3, x_119, x_120);
x_122 = l_Lean_mkConst(x_121, x_117);
x_123 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_124 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_125 = l_Lean_mkApp4(x_122, x_116, x_93, x_123, x_124);
x_126 = l_Lean_mkPropEq(x_94, x_118);
x_127 = l_Lean_Meta_mkExpectedPropHint(x_125, x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_118);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
else
{
uint8_t x_131; 
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_131 = !lean_is_exclusive(x_100);
if (x_131 == 0)
{
return x_100;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_100, 0);
lean_inc(x_132);
lean_dec(x_100);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = l_Int_Linear_Poly_div(x_96, x_95);
lean_inc_ref(x_134);
x_135 = l_Int_Linear_Poly_toExpr(x_134);
x_136 = l_Int_Linear_instBEqExpr_beq(x_2, x_135);
lean_dec_ref(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
lean_dec(x_92);
lean_inc_ref(x_134);
x_137 = l_Int_Linear_Poly_denoteExpr___redArg(x_89, x_134);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
x_139 = lean_int_ediv(x_6, x_96);
lean_dec(x_6);
x_140 = lean_int_dec_le(x_4, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_141 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10;
x_142 = l_Lean_Level_ofNat(x_5);
x_143 = lean_box(0);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Lean_Expr_const___override(x_141, x_144);
lean_inc_ref(x_3);
x_146 = l_Lean_Name_mkStr1(x_3);
x_147 = l_Lean_Expr_const___override(x_146, x_143);
x_148 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
lean_inc_ref(x_3);
x_149 = l_Lean_Name_mkStr2(x_3, x_148);
x_150 = l_Lean_Expr_const___override(x_149, x_143);
x_151 = lean_int_neg(x_139);
lean_dec(x_139);
x_152 = l_Int_toNat(x_151);
lean_dec(x_151);
x_153 = l_Lean_instToExprInt_mkNat(x_152);
x_154 = l_Lean_mkApp3(x_145, x_147, x_150, x_153);
x_36 = x_96;
x_37 = x_138;
x_38 = x_94;
x_39 = x_134;
x_40 = x_93;
x_41 = lean_box(0);
x_42 = x_154;
goto block_88;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = l_Int_toNat(x_139);
lean_dec(x_139);
x_156 = l_Lean_instToExprInt_mkNat(x_155);
x_36 = x_96;
x_37 = x_138;
x_38 = x_94;
x_39 = x_134;
x_40 = x_93;
x_41 = lean_box(0);
x_42 = x_156;
goto block_88;
}
}
else
{
uint8_t x_157; 
lean_dec_ref(x_134);
lean_dec(x_96);
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_157 = !lean_is_exclusive(x_137);
if (x_157 == 0)
{
return x_137;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_137, 0);
lean_inc(x_158);
lean_dec(x_137);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
return x_159;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; 
lean_dec_ref(x_134);
lean_dec(x_96);
lean_dec_ref(x_94);
lean_dec_ref(x_93);
lean_dec_ref(x_89);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_160 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_161 = lean_alloc_ctor(0, 1, 0);
} else {
 x_161 = x_92;
}
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
}
}
}
else
{
uint8_t x_180; 
lean_dec_ref(x_89);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_180 = !lean_is_exclusive(x_90);
if (x_180 == 0)
{
return x_90;
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_90, 0);
lean_inc(x_181);
lean_dec(x_90);
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_181);
return x_182;
}
}
block_22:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc_ref(x_14);
x_17 = l_Lean_mkPropEq(x_13, x_14);
x_18 = l_Lean_Meta_mkExpectedPropHint(x_15, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_34 = l_Lean_mkApp7(x_24, x_31, x_30, x_26, x_29, x_23, x_32, x_33);
x_13 = x_25;
x_14 = x_27;
x_15 = x_34;
x_16 = lean_box(0);
goto block_22;
}
block_88:
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_inc_ref(x_42);
x_43 = l_Lean_mkIntDvd(x_42, x_37);
x_44 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__18;
x_45 = lean_int_dec_eq(x_36, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_49 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__0;
lean_inc_ref(x_3);
x_50 = l_Lean_Name_mkStr3(x_3, x_48, x_49);
x_51 = lean_box(0);
x_52 = l_Lean_mkConst(x_50, x_51);
x_53 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_54 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_39);
x_55 = lean_int_dec_le(x_4, x_36);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_56 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10;
x_57 = l_Lean_Level_ofNat(x_5);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_51);
x_59 = l_Lean_Expr_const___override(x_56, x_58);
lean_inc_ref(x_3);
x_60 = l_Lean_Name_mkStr1(x_3);
x_61 = l_Lean_Expr_const___override(x_60, x_51);
x_62 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
x_63 = l_Lean_Name_mkStr2(x_3, x_62);
x_64 = l_Lean_Expr_const___override(x_63, x_51);
x_65 = lean_int_neg(x_36);
lean_dec(x_36);
x_66 = l_Int_toNat(x_65);
lean_dec(x_65);
x_67 = l_Lean_instToExprInt_mkNat(x_66);
x_68 = l_Lean_mkApp3(x_59, x_61, x_64, x_67);
x_23 = x_54;
x_24 = x_52;
x_25 = x_38;
x_26 = x_53;
x_27 = x_43;
x_28 = lean_box(0);
x_29 = x_42;
x_30 = x_40;
x_31 = x_47;
x_32 = x_68;
goto block_35;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_3);
x_69 = l_Int_toNat(x_36);
lean_dec(x_36);
x_70 = l_Lean_instToExprInt_mkNat(x_69);
x_23 = x_54;
x_24 = x_52;
x_25 = x_38;
x_26 = x_53;
x_27 = x_43;
x_28 = lean_box(0);
x_29 = x_42;
x_30 = x_40;
x_31 = x_47;
x_32 = x_70;
goto block_35;
}
}
else
{
uint8_t x_71; 
lean_dec_ref(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec(x_36);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_71 = !lean_is_exclusive(x_46);
if (x_71 == 0)
{
return x_46;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_46, 0);
lean_inc(x_72);
lean_dec(x_46);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; 
lean_dec_ref(x_42);
lean_dec(x_36);
x_74 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_77 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__1;
x_78 = l_Lean_Name_mkStr3(x_3, x_76, x_77);
x_79 = lean_box(0);
x_80 = l_Lean_mkConst(x_78, x_79);
x_81 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_82 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_39);
x_83 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_84 = l_Lean_mkApp5(x_80, x_75, x_40, x_81, x_82, x_83);
x_13 = x_38;
x_14 = x_43;
x_15 = x_84;
x_16 = lean_box(0);
goto block_22;
}
else
{
uint8_t x_85; 
lean_dec_ref(x_43);
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_85 = !lean_is_exclusive(x_74);
if (x_85 == 0)
{
return x_74;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_74, 0);
lean_inc(x_86);
lean_dec(x_74);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_7 = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = lean_box(0);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
x_18 = lean_int_dec_eq(x_13, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_7);
x_19 = l_Lean_instInhabitedExpr;
x_20 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___boxed), 12, 6);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_14);
lean_closure_set(x_21, 2, x_20);
lean_closure_set(x_21, 3, x_17);
lean_closure_set(x_21, 4, x_16);
lean_closure_set(x_21, 5, x_13);
x_22 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_23 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_15, x_22, x_21, x_2, x_3, x_4, x_5);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_24 = lean_box(0);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec_ref(x_25);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
x_35 = lean_int_dec_eq(x_30, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = l_Lean_instInhabitedExpr;
x_37 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___boxed), 12, 6);
lean_closure_set(x_38, 0, x_36);
lean_closure_set(x_38, 1, x_31);
lean_closure_set(x_38, 2, x_37);
lean_closure_set(x_38, 3, x_34);
lean_closure_set(x_38, 4, x_33);
lean_closure_set(x_38, 5, x_30);
x_39 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_40 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_32, x_39, x_38, x_2, x_3, x_4, x_5);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_43 = !lean_is_exclusive(x_7);
if (x_43 == 0)
{
return x_7;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_7, 0);
lean_inc(x_44);
lean_dec(x_7);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
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
lean_inc_ref(x_4);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expr", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_of_norm_eq", 13, 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Int_Linear_Expr_norm(x_1);
lean_inc_ref(x_9);
x_10 = l_Int_Linear_Poly_toExpr(x_9);
x_11 = l_Int_Linear_instBEqExpr_beq(x_1, x_10);
lean_dec_ref(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_inc_ref(x_3);
x_12 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_14, 0, x_3);
lean_inc_ref(x_1);
lean_inc_ref(x_14);
x_15 = l_Int_Linear_Expr_denoteExpr___redArg(x_14, x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc_ref(x_9);
x_17 = l_Int_Linear_Poly_denoteExpr___redArg(x_14, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_21 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__0;
x_22 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__1;
x_23 = l_Lean_Name_mkStr4(x_2, x_20, x_21, x_22);
x_24 = lean_box(0);
x_25 = l_Lean_mkConst(x_23, x_24);
x_26 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_27 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_9);
x_28 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_29 = l_Lean_mkApp4(x_25, x_13, x_26, x_27, x_28);
lean_inc(x_19);
x_30 = l_Lean_mkIntEq(x_16, x_19);
x_31 = l_Lean_Meta_mkExpectedPropHint(x_29, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_17, 0, x_33);
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_34 = lean_ctor_get(x_17, 0);
lean_inc(x_34);
lean_dec(x_17);
x_35 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_36 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__0;
x_37 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__1;
x_38 = l_Lean_Name_mkStr4(x_2, x_35, x_36, x_37);
x_39 = lean_box(0);
x_40 = l_Lean_mkConst(x_38, x_39);
x_41 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_42 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_9);
x_43 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_44 = l_Lean_mkApp4(x_40, x_13, x_41, x_42, x_43);
lean_inc(x_34);
x_45 = l_Lean_mkIntEq(x_16, x_34);
x_46 = l_Lean_Meta_mkExpectedPropHint(x_44, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_50 = !lean_is_exclusive(x_17);
if (x_50 == 0)
{
return x_17;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_17, 0);
lean_inc(x_51);
lean_dec(x_17);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_53 = !lean_is_exclusive(x_15);
if (x_53 == 0)
{
return x_15;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_15, 0);
lean_inc(x_54);
lean_dec(x_15);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec_ref(x_9);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_56 = !lean_is_exclusive(x_12);
if (x_56 == 0)
{
return x_12;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_12, 0);
lean_inc(x_57);
lean_dec(x_12);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___boxed), 8, 2);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_14 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_10, x_13, x_12, x_2, x_3, x_4, x_5);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
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
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__4 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__4);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__5 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__5);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__7 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__7);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__8 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__8);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__9 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__9);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__11 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__11);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__12 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__12);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__13 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__13);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__15 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__15);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__16 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__16);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__17 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__17();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__17);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__18 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__18();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__18);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__19 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__19();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__19);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__20 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__20();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__20);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__21 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__21();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__21);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__22 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__22();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__22);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__23 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__23();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__23);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__24 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__24();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__24);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__25 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__25();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__25);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__26 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__26();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__26);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0);
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__0);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__3);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__4 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__4);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__0);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__3);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__4 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__4);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__5 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__5);
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__6 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__6);
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
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__0);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__1);
l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__2);
l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__0);
l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
