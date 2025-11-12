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
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45;
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
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30;
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
lean_inc_ref(x_4);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_eagerReflBoolTrue;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Linear", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_eq_var_const", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_eq_false_of_divCoeff", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instNegInt", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6;
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_eq_coeff", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_eq", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("norm_eq_var", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("True", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_eq_true", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_eq_false", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44;
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
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = lean_box(0);
if (lean_is_scalar(x_9)) {
 x_11 = lean_alloc_ctor(0, 1, 0);
} else {
 x_11 = x_9;
}
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_13 = x_8;
} else {
 lean_dec_ref(x_8);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_16 = x_12;
} else {
 lean_dec_ref(x_12);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_19 = x_14;
} else {
 lean_dec_ref(x_14);
 x_19 = lean_box(0);
}
x_20 = l_Lean_instInhabitedExpr;
lean_inc(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_18);
lean_inc(x_15);
lean_inc_ref(x_21);
x_22 = l_Int_Linear_Expr_denoteExpr___redArg(x_21, x_15);
if (lean_obj_tag(x_22) == 0)
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
lean_inc(x_17);
lean_inc_ref(x_21);
x_25 = l_Int_Linear_Expr_denoteExpr___redArg(x_21, x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_193; uint8_t x_283; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = l_Lean_mkIntEq(x_23, x_26);
lean_inc(x_17);
lean_inc(x_15);
x_94 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_94, 0, x_15);
lean_ctor_set(x_94, 1, x_17);
x_95 = l_Int_Linear_Expr_norm(x_94);
lean_dec_ref(x_94);
x_283 = l_Int_Linear_Poly_isUnsatEq(x_95);
if (x_283 == 0)
{
uint8_t x_284; 
x_284 = l_Int_Linear_Poly_isValidEq(x_95);
if (x_284 == 0)
{
lean_object* x_285; uint8_t x_286; 
lean_inc_ref(x_95);
x_285 = l_Int_Linear_Poly_toExpr(x_95);
x_286 = l_Int_Linear_instBEqExpr_beq(x_285, x_15);
lean_dec_ref(x_285);
if (x_286 == 0)
{
x_193 = x_286;
goto block_282;
}
else
{
lean_object* x_287; uint8_t x_288; 
x_287 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36;
x_288 = l_Int_Linear_instBEqExpr_beq(x_17, x_287);
x_193 = x_288;
goto block_282;
}
}
else
{
lean_object* x_289; 
lean_dec_ref(x_95);
lean_dec(x_27);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_9);
x_289 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_289) == 0)
{
uint8_t x_290; 
x_290 = !lean_is_exclusive(x_289);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_291 = lean_ctor_get(x_289, 0);
x_292 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39;
x_293 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42;
x_294 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_295 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_17);
x_296 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_297 = l_Lean_mkApp4(x_293, x_291, x_294, x_295, x_296);
x_298 = l_Lean_mkPropEq(x_28, x_292);
x_299 = l_Lean_Meta_mkExpectedPropHint(x_297, x_298);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_292);
lean_ctor_set(x_300, 1, x_299);
x_301 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_289, 0, x_301);
return x_289;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_302 = lean_ctor_get(x_289, 0);
lean_inc(x_302);
lean_dec(x_289);
x_303 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39;
x_304 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42;
x_305 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_306 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_17);
x_307 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_308 = l_Lean_mkApp4(x_304, x_302, x_305, x_306, x_307);
x_309 = l_Lean_mkPropEq(x_28, x_303);
x_310 = l_Lean_Meta_mkExpectedPropHint(x_308, x_309);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_303);
lean_ctor_set(x_311, 1, x_310);
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_311);
x_313 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_313, 0, x_312);
return x_313;
}
}
else
{
uint8_t x_314; 
lean_dec_ref(x_28);
lean_dec(x_17);
lean_dec(x_15);
x_314 = !lean_is_exclusive(x_289);
if (x_314 == 0)
{
return x_289;
}
else
{
lean_object* x_315; lean_object* x_316; 
x_315 = lean_ctor_get(x_289, 0);
lean_inc(x_315);
lean_dec(x_289);
x_316 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_316, 0, x_315);
return x_316;
}
}
}
}
else
{
lean_object* x_317; 
lean_dec_ref(x_95);
lean_dec(x_27);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_9);
x_317 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_317) == 0)
{
uint8_t x_318; 
x_318 = !lean_is_exclusive(x_317);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_319 = lean_ctor_get(x_317, 0);
x_320 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9;
x_321 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45;
x_322 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_323 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_17);
x_324 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_325 = l_Lean_mkApp4(x_321, x_319, x_322, x_323, x_324);
x_326 = l_Lean_mkPropEq(x_28, x_320);
x_327 = l_Lean_Meta_mkExpectedPropHint(x_325, x_326);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_320);
lean_ctor_set(x_328, 1, x_327);
x_329 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_317, 0, x_329);
return x_317;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_330 = lean_ctor_get(x_317, 0);
lean_inc(x_330);
lean_dec(x_317);
x_331 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9;
x_332 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45;
x_333 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_334 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_17);
x_335 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_336 = l_Lean_mkApp4(x_332, x_330, x_333, x_334, x_335);
x_337 = l_Lean_mkPropEq(x_28, x_331);
x_338 = l_Lean_Meta_mkExpectedPropHint(x_336, x_337);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_331);
lean_ctor_set(x_339, 1, x_338);
x_340 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_340, 0, x_339);
x_341 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_341, 0, x_340);
return x_341;
}
}
else
{
uint8_t x_342; 
lean_dec_ref(x_28);
lean_dec(x_17);
lean_dec(x_15);
x_342 = !lean_is_exclusive(x_317);
if (x_342 == 0)
{
return x_317;
}
else
{
lean_object* x_343; lean_object* x_344; 
x_343 = lean_ctor_get(x_317, 0);
lean_inc(x_343);
lean_dec(x_317);
x_344 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_344, 0, x_343);
return x_344;
}
}
}
block_43:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_37 = l_Lean_mkApp5(x_31, x_29, x_34, x_30, x_35, x_36);
lean_inc_ref(x_33);
x_38 = l_Lean_mkPropEq(x_28, x_33);
x_39 = l_Lean_Meta_mkExpectedPropHint(x_37, x_38);
if (lean_is_scalar(x_19)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_19;
}
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_39);
if (lean_is_scalar(x_13)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_13;
}
lean_ctor_set(x_41, 0, x_40);
if (lean_is_scalar(x_27)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_27;
}
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
block_59:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_53 = l_Lean_mkApp6(x_47, x_50, x_49, x_46, x_45, x_51, x_52);
lean_inc_ref(x_48);
x_54 = l_Lean_mkPropEq(x_28, x_48);
x_55 = l_Lean_Meta_mkExpectedPropHint(x_53, x_54);
if (lean_is_scalar(x_16)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_16;
}
lean_ctor_set(x_56, 0, x_48);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
if (lean_is_scalar(x_24)) {
 x_58 = lean_alloc_ctor(0, 1, 0);
} else {
 x_58 = x_24;
}
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
block_93:
{
lean_object* x_63; 
x_63 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_65 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_62);
x_66 = l_Lean_mkIntEq(x_61, x_62);
x_67 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5;
x_68 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_69 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_17);
x_70 = l_Lean_mkNatLit(x_60);
x_71 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_72 = l_Lean_mkApp6(x_67, x_65, x_68, x_69, x_70, x_62, x_71);
lean_inc_ref(x_66);
x_73 = l_Lean_mkPropEq(x_28, x_66);
x_74 = l_Lean_Meta_mkExpectedPropHint(x_72, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_66);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_63, 0, x_76);
return x_63;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_77 = lean_ctor_get(x_63, 0);
lean_inc(x_77);
lean_dec(x_63);
lean_inc_ref(x_62);
x_78 = l_Lean_mkIntEq(x_61, x_62);
x_79 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5;
x_80 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_81 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_17);
x_82 = l_Lean_mkNatLit(x_60);
x_83 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_84 = l_Lean_mkApp6(x_79, x_77, x_80, x_81, x_82, x_62, x_83);
lean_inc_ref(x_78);
x_85 = l_Lean_mkPropEq(x_28, x_78);
x_86 = l_Lean_Meta_mkExpectedPropHint(x_84, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_78);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec_ref(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_28);
lean_dec(x_17);
lean_dec(x_15);
x_90 = !lean_is_exclusive(x_63);
if (x_90 == 0)
{
return x_63;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_63, 0);
lean_inc(x_91);
lean_dec(x_63);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
block_192:
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Int_Linear_Poly_gcdCoeffs_x27(x_95);
x_102 = lean_unsigned_to_nat(1u);
x_103 = lean_nat_dec_eq(x_101, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = l_Int_Linear_Poly_getConst(x_95);
x_105 = lean_nat_to_int(x_101);
x_106 = lean_int_emod(x_104, x_105);
lean_dec(x_104);
x_107 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6;
x_108 = lean_int_dec_eq(x_106, x_107);
lean_dec(x_106);
if (x_108 == 0)
{
lean_object* x_109; 
lean_dec_ref(x_95);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec(x_16);
x_109 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_18, x_96, x_97, x_98, x_99);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
x_111 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9;
x_112 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12;
x_113 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_114 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_17);
x_115 = lean_int_dec_le(x_107, x_105);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
x_117 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20;
x_118 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
x_119 = lean_int_neg(x_105);
lean_dec(x_105);
x_120 = l_Int_toNat(x_119);
lean_dec(x_119);
x_121 = l_Lean_instToExprInt_mkNat(x_120);
x_122 = l_Lean_mkApp3(x_116, x_117, x_118, x_121);
x_29 = x_110;
x_30 = x_114;
x_31 = x_112;
x_32 = lean_box(0);
x_33 = x_111;
x_34 = x_113;
x_35 = x_122;
goto block_43;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = l_Int_toNat(x_105);
lean_dec(x_105);
x_124 = l_Lean_instToExprInt_mkNat(x_123);
x_29 = x_110;
x_30 = x_114;
x_31 = x_112;
x_32 = lean_box(0);
x_33 = x_111;
x_34 = x_113;
x_35 = x_124;
goto block_43;
}
}
else
{
uint8_t x_125; 
lean_dec(x_105);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
x_125 = !lean_is_exclusive(x_109);
if (x_125 == 0)
{
return x_109;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_109, 0);
lean_inc(x_126);
lean_dec(x_109);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_27);
lean_dec(x_19);
lean_dec(x_13);
x_128 = l_Int_Linear_Poly_div(x_105, x_95);
lean_inc_ref(x_128);
x_129 = l_Int_Linear_Poly_denoteExpr___redArg(x_21, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_18, x_96, x_97, x_98, x_99);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24;
x_134 = l_Lean_mkIntEq(x_130, x_133);
x_135 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27;
x_136 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_137 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_17);
x_138 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_128);
x_139 = lean_int_dec_le(x_107, x_105);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_140 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
x_141 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20;
x_142 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
x_143 = lean_int_neg(x_105);
lean_dec(x_105);
x_144 = l_Int_toNat(x_143);
lean_dec(x_143);
x_145 = l_Lean_instToExprInt_mkNat(x_144);
x_146 = l_Lean_mkApp3(x_140, x_141, x_142, x_145);
x_44 = lean_box(0);
x_45 = x_138;
x_46 = x_137;
x_47 = x_135;
x_48 = x_134;
x_49 = x_136;
x_50 = x_132;
x_51 = x_146;
goto block_59;
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = l_Int_toNat(x_105);
lean_dec(x_105);
x_148 = l_Lean_instToExprInt_mkNat(x_147);
x_44 = lean_box(0);
x_45 = x_138;
x_46 = x_137;
x_47 = x_135;
x_48 = x_134;
x_49 = x_136;
x_50 = x_132;
x_51 = x_148;
goto block_59;
}
}
else
{
uint8_t x_149; 
lean_dec(x_130);
lean_dec_ref(x_128);
lean_dec(x_105);
lean_dec_ref(x_28);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_149 = !lean_is_exclusive(x_131);
if (x_149 == 0)
{
return x_131;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_131, 0);
lean_inc(x_150);
lean_dec(x_131);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_dec_ref(x_128);
lean_dec(x_105);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_28);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_152 = !lean_is_exclusive(x_129);
if (x_152 == 0)
{
return x_129;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_129, 0);
lean_inc(x_153);
lean_dec(x_129);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
}
}
}
else
{
lean_object* x_155; 
lean_dec(x_101);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_inc_ref(x_95);
x_155 = l_Int_Linear_Poly_denoteExpr___redArg(x_21, x_95);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_dec_ref(x_155);
x_157 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_18, x_96, x_97, x_98, x_99);
if (lean_obj_tag(x_157) == 0)
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_159 = lean_ctor_get(x_157, 0);
x_160 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24;
x_161 = l_Lean_mkIntEq(x_156, x_160);
x_162 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30;
x_163 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_164 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_17);
x_165 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_95);
x_166 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_167 = l_Lean_mkApp5(x_162, x_159, x_163, x_164, x_165, x_166);
lean_inc_ref(x_161);
x_168 = l_Lean_mkPropEq(x_28, x_161);
x_169 = l_Lean_Meta_mkExpectedPropHint(x_167, x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_161);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_157, 0, x_171);
return x_157;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_172 = lean_ctor_get(x_157, 0);
lean_inc(x_172);
lean_dec(x_157);
x_173 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24;
x_174 = l_Lean_mkIntEq(x_156, x_173);
x_175 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30;
x_176 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_177 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_17);
x_178 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_95);
x_179 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_180 = l_Lean_mkApp5(x_175, x_172, x_176, x_177, x_178, x_179);
lean_inc_ref(x_174);
x_181 = l_Lean_mkPropEq(x_28, x_174);
x_182 = l_Lean_Meta_mkExpectedPropHint(x_180, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_174);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
x_185 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_185, 0, x_184);
return x_185;
}
}
else
{
uint8_t x_186; 
lean_dec(x_156);
lean_dec_ref(x_95);
lean_dec_ref(x_28);
lean_dec(x_17);
lean_dec(x_15);
x_186 = !lean_is_exclusive(x_157);
if (x_186 == 0)
{
return x_157;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_157, 0);
lean_inc(x_187);
lean_dec(x_157);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
return x_188;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec_ref(x_95);
lean_dec_ref(x_28);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
x_189 = !lean_is_exclusive(x_155);
if (x_189 == 0)
{
return x_155;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_155, 0);
lean_inc(x_190);
lean_dec(x_155);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_190);
return x_191;
}
}
}
}
block_282:
{
if (x_193 == 0)
{
lean_dec(x_9);
if (lean_obj_tag(x_95) == 0)
{
x_96 = x_2;
x_97 = x_3;
x_98 = x_4;
x_99 = x_5;
x_100 = lean_box(0);
goto block_192;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_194 = lean_ctor_get(x_95, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_95, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_95, 2);
lean_inc_ref(x_196);
x_197 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31;
x_198 = lean_int_dec_eq(x_194, x_197);
lean_dec(x_194);
if (x_198 == 0)
{
lean_dec_ref(x_196);
lean_dec(x_195);
x_96 = x_2;
x_97 = x_3;
x_98 = x_4;
x_99 = x_5;
x_100 = lean_box(0);
goto block_192;
}
else
{
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
lean_dec_ref(x_95);
lean_dec(x_27);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
x_199 = lean_ctor_get(x_196, 0);
lean_inc(x_199);
lean_dec_ref(x_196);
x_200 = lean_array_get_borrowed(x_20, x_18, x_195);
x_201 = lean_int_neg(x_199);
lean_dec(x_199);
x_202 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6;
x_203 = lean_int_dec_le(x_202, x_201);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_204 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
x_205 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20;
x_206 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
x_207 = lean_int_neg(x_201);
lean_dec(x_201);
x_208 = l_Int_toNat(x_207);
lean_dec(x_207);
x_209 = l_Lean_instToExprInt_mkNat(x_208);
x_210 = l_Lean_mkApp3(x_204, x_205, x_206, x_209);
lean_inc_ref(x_200);
x_60 = x_195;
x_61 = x_200;
x_62 = x_210;
goto block_93;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = l_Int_toNat(x_201);
lean_dec(x_201);
x_212 = l_Lean_instToExprInt_mkNat(x_211);
lean_inc_ref(x_200);
x_60 = x_195;
x_61 = x_200;
x_62 = x_212;
goto block_93;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_213 = lean_ctor_get(x_196, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_196, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_196, 2);
lean_inc_ref(x_215);
lean_dec_ref(x_196);
x_216 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32;
x_217 = lean_int_dec_eq(x_213, x_216);
lean_dec(x_213);
if (x_217 == 0)
{
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec(x_195);
x_96 = x_2;
x_97 = x_3;
x_98 = x_4;
x_99 = x_5;
x_100 = lean_box(0);
goto block_192;
}
else
{
if (lean_obj_tag(x_215) == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_215);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_219 = lean_ctor_get(x_215, 0);
x_220 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6;
x_221 = lean_int_dec_eq(x_219, x_220);
lean_dec(x_219);
if (x_221 == 0)
{
lean_free_object(x_215);
lean_dec(x_214);
lean_dec(x_195);
x_96 = x_2;
x_97 = x_3;
x_98 = x_4;
x_99 = x_5;
x_100 = lean_box(0);
goto block_192;
}
else
{
lean_object* x_222; 
lean_dec_ref(x_95);
lean_dec(x_27);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_inc(x_18);
x_222 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_222) == 0)
{
uint8_t x_223; 
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_224 = lean_ctor_get(x_222, 0);
x_225 = lean_array_get(x_20, x_18, x_195);
x_226 = lean_array_get(x_20, x_18, x_214);
lean_dec(x_18);
x_227 = l_Lean_mkIntEq(x_225, x_226);
x_228 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35;
x_229 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_230 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_17);
x_231 = l_Lean_mkNatLit(x_195);
x_232 = l_Lean_mkNatLit(x_214);
x_233 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_234 = l_Lean_mkApp6(x_228, x_224, x_229, x_230, x_231, x_232, x_233);
lean_inc_ref(x_227);
x_235 = l_Lean_mkPropEq(x_28, x_227);
x_236 = l_Lean_Meta_mkExpectedPropHint(x_234, x_235);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_227);
lean_ctor_set(x_237, 1, x_236);
lean_ctor_set_tag(x_215, 1);
lean_ctor_set(x_215, 0, x_237);
lean_ctor_set(x_222, 0, x_215);
return x_222;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_238 = lean_ctor_get(x_222, 0);
lean_inc(x_238);
lean_dec(x_222);
x_239 = lean_array_get(x_20, x_18, x_195);
x_240 = lean_array_get(x_20, x_18, x_214);
lean_dec(x_18);
x_241 = l_Lean_mkIntEq(x_239, x_240);
x_242 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35;
x_243 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_244 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_17);
x_245 = l_Lean_mkNatLit(x_195);
x_246 = l_Lean_mkNatLit(x_214);
x_247 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_248 = l_Lean_mkApp6(x_242, x_238, x_243, x_244, x_245, x_246, x_247);
lean_inc_ref(x_241);
x_249 = l_Lean_mkPropEq(x_28, x_241);
x_250 = l_Lean_Meta_mkExpectedPropHint(x_248, x_249);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_241);
lean_ctor_set(x_251, 1, x_250);
lean_ctor_set_tag(x_215, 1);
lean_ctor_set(x_215, 0, x_251);
x_252 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_252, 0, x_215);
return x_252;
}
}
else
{
uint8_t x_253; 
lean_free_object(x_215);
lean_dec(x_214);
lean_dec(x_195);
lean_dec_ref(x_28);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
x_253 = !lean_is_exclusive(x_222);
if (x_253 == 0)
{
return x_222;
}
else
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_222, 0);
lean_inc(x_254);
lean_dec(x_222);
x_255 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_255, 0, x_254);
return x_255;
}
}
}
}
else
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_256 = lean_ctor_get(x_215, 0);
lean_inc(x_256);
lean_dec(x_215);
x_257 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6;
x_258 = lean_int_dec_eq(x_256, x_257);
lean_dec(x_256);
if (x_258 == 0)
{
lean_dec(x_214);
lean_dec(x_195);
x_96 = x_2;
x_97 = x_3;
x_98 = x_4;
x_99 = x_5;
x_100 = lean_box(0);
goto block_192;
}
else
{
lean_object* x_259; 
lean_dec_ref(x_95);
lean_dec(x_27);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_inc(x_18);
x_259 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 x_261 = x_259;
} else {
 lean_dec_ref(x_259);
 x_261 = lean_box(0);
}
x_262 = lean_array_get(x_20, x_18, x_195);
x_263 = lean_array_get(x_20, x_18, x_214);
lean_dec(x_18);
x_264 = l_Lean_mkIntEq(x_262, x_263);
x_265 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35;
x_266 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_15);
x_267 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_17);
x_268 = l_Lean_mkNatLit(x_195);
x_269 = l_Lean_mkNatLit(x_214);
x_270 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_271 = l_Lean_mkApp6(x_265, x_260, x_266, x_267, x_268, x_269, x_270);
lean_inc_ref(x_264);
x_272 = l_Lean_mkPropEq(x_28, x_264);
x_273 = l_Lean_Meta_mkExpectedPropHint(x_271, x_272);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_264);
lean_ctor_set(x_274, 1, x_273);
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_274);
if (lean_is_scalar(x_261)) {
 x_276 = lean_alloc_ctor(0, 1, 0);
} else {
 x_276 = x_261;
}
lean_ctor_set(x_276, 0, x_275);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_214);
lean_dec(x_195);
lean_dec_ref(x_28);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
x_277 = lean_ctor_get(x_259, 0);
lean_inc(x_277);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 x_278 = x_259;
} else {
 lean_dec_ref(x_259);
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
lean_dec_ref(x_215);
lean_dec(x_214);
lean_dec(x_195);
x_96 = x_2;
x_97 = x_3;
x_98 = x_4;
x_99 = x_5;
x_100 = lean_box(0);
goto block_192;
}
}
}
}
}
}
else
{
lean_object* x_280; lean_object* x_281; 
lean_dec_ref(x_95);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_280 = lean_box(0);
if (lean_is_scalar(x_9)) {
 x_281 = lean_alloc_ctor(0, 1, 0);
} else {
 x_281 = x_9;
}
lean_ctor_set(x_281, 0, x_280);
return x_281;
}
}
}
else
{
uint8_t x_345; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_345 = !lean_is_exclusive(x_25);
if (x_345 == 0)
{
return x_25;
}
else
{
lean_object* x_346; lean_object* x_347; 
x_346 = lean_ctor_get(x_25, 0);
lean_inc(x_346);
lean_dec(x_25);
x_347 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_347, 0, x_346);
return x_347;
}
}
}
else
{
uint8_t x_348; 
lean_dec_ref(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_348 = !lean_is_exclusive(x_22);
if (x_348 == 0)
{
return x_22;
}
else
{
lean_object* x_349; lean_object* x_350; 
x_349 = lean_ctor_get(x_22, 0);
lean_inc(x_349);
lean_dec(x_22);
x_350 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_350, 0, x_349);
return x_350;
}
}
}
}
else
{
uint8_t x_351; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_351 = !lean_is_exclusive(x_7);
if (x_351 == 0)
{
return x_7;
}
else
{
lean_object* x_352; lean_object* x_353; 
x_352 = lean_ctor_get(x_7, 0);
lean_inc(x_352);
lean_dec(x_7);
x_353 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_353, 0, x_352);
return x_353;
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
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
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
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
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
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
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
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
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
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
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
lean_inc_ref(x_8);
x_12 = l_Lean_mkPropEq(x_9, x_8);
x_13 = l_Lean_Meta_mkExpectedPropHint(x_10, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
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
x_27 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_28 = l_Lean_mkApp6(x_22, x_19, x_21, x_24, x_23, x_26, x_27);
x_8 = x_18;
x_9 = x_20;
x_10 = x_28;
x_11 = lean_box(0);
goto block_17;
}
block_41:
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_40 = l_Lean_mkApp6(x_36, x_35, x_33, x_30, x_37, x_38, x_39);
x_8 = x_31;
x_9 = x_32;
x_10 = x_40;
x_11 = lean_box(0);
goto block_17;
}
block_107:
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_Int_Linear_Poly_div(x_51, x_43);
lean_inc_ref(x_53);
x_54 = l_Int_Linear_Poly_denoteExpr___redArg(x_44, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = l_Lean_mkIntLit(x_42);
x_57 = l_Lean_mkIntLE(x_55, x_56);
if (x_52 == 0)
{
lean_object* x_58; 
x_58 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_48, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_box(0);
x_61 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2;
x_62 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_50);
x_63 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_45);
x_64 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_53);
x_65 = lean_int_dec_le(x_42, x_51);
lean_dec(x_42);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_66 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15;
x_67 = l_Lean_Level_ofNat(x_49);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_60);
x_69 = l_Lean_Expr_const___override(x_66, x_68);
x_70 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20;
x_71 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
x_72 = lean_int_neg(x_51);
lean_dec(x_51);
x_73 = l_Int_toNat(x_72);
lean_dec(x_72);
x_74 = l_Lean_instToExprInt_mkNat(x_73);
x_75 = l_Lean_mkApp3(x_69, x_70, x_71, x_74);
x_30 = x_63;
x_31 = x_57;
x_32 = x_46;
x_33 = x_62;
x_34 = lean_box(0);
x_35 = x_59;
x_36 = x_61;
x_37 = x_64;
x_38 = x_75;
goto block_41;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Int_toNat(x_51);
lean_dec(x_51);
x_77 = l_Lean_instToExprInt_mkNat(x_76);
x_30 = x_63;
x_31 = x_57;
x_32 = x_46;
x_33 = x_62;
x_34 = lean_box(0);
x_35 = x_59;
x_36 = x_61;
x_37 = x_64;
x_38 = x_77;
goto block_41;
}
}
else
{
uint8_t x_78; 
lean_dec_ref(x_57);
lean_dec_ref(x_53);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_46);
lean_dec_ref(x_45);
lean_dec(x_42);
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
x_81 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_48, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = lean_box(0);
x_84 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5;
x_85 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_50);
x_86 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_45);
x_87 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_53);
x_88 = lean_int_dec_le(x_42, x_51);
lean_dec(x_42);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_89 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15;
x_90 = l_Lean_Level_ofNat(x_49);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_83);
x_92 = l_Lean_Expr_const___override(x_89, x_91);
x_93 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20;
x_94 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
x_95 = lean_int_neg(x_51);
lean_dec(x_51);
x_96 = l_Int_toNat(x_95);
lean_dec(x_95);
x_97 = l_Lean_instToExprInt_mkNat(x_96);
x_98 = l_Lean_mkApp3(x_92, x_93, x_94, x_97);
x_18 = x_57;
x_19 = x_82;
x_20 = x_46;
x_21 = x_85;
x_22 = x_84;
x_23 = x_87;
x_24 = x_86;
x_25 = lean_box(0);
x_26 = x_98;
goto block_29;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Int_toNat(x_51);
lean_dec(x_51);
x_100 = l_Lean_instToExprInt_mkNat(x_99);
x_18 = x_57;
x_19 = x_82;
x_20 = x_46;
x_21 = x_85;
x_22 = x_84;
x_23 = x_87;
x_24 = x_86;
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
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_46);
lean_dec_ref(x_45);
lean_dec(x_42);
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
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_48);
lean_dec_ref(x_46);
lean_dec_ref(x_45);
lean_dec(x_42);
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
x_115 = l_Int_Linear_Poly_gcdCoeffs_x27(x_108);
x_116 = lean_unsigned_to_nat(1u);
x_117 = lean_nat_dec_eq(x_115, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_118 = l_Int_Linear_Poly_getConst(x_108);
x_119 = lean_nat_to_int(x_115);
x_120 = lean_int_emod(x_118, x_119);
lean_dec(x_118);
x_121 = lean_unsigned_to_nat(0u);
x_122 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6;
x_123 = lean_int_dec_eq(x_120, x_122);
lean_dec(x_120);
if (x_123 == 0)
{
uint8_t x_124; 
x_124 = 1;
x_42 = x_122;
x_43 = x_108;
x_44 = x_109;
x_45 = x_112;
x_46 = x_111;
x_47 = lean_box(0);
x_48 = x_113;
x_49 = x_121;
x_50 = x_114;
x_51 = x_119;
x_52 = x_124;
goto block_107;
}
else
{
x_42 = x_122;
x_43 = x_108;
x_44 = x_109;
x_45 = x_112;
x_46 = x_111;
x_47 = lean_box(0);
x_48 = x_113;
x_49 = x_121;
x_50 = x_114;
x_51 = x_119;
x_52 = x_117;
goto block_107;
}
}
else
{
lean_object* x_125; 
lean_dec(x_115);
lean_inc_ref(x_108);
x_125 = l_Int_Linear_Poly_denoteExpr___redArg(x_109, x_108);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_113, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24;
x_131 = l_Lean_mkIntLE(x_126, x_130);
x_132 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8;
x_133 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_114);
x_134 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_112);
x_135 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_108);
x_136 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_137 = l_Lean_mkApp5(x_132, x_129, x_133, x_134, x_135, x_136);
lean_inc_ref(x_131);
x_138 = l_Lean_mkPropEq(x_111, x_131);
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
x_143 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24;
x_144 = l_Lean_mkIntLE(x_126, x_143);
x_145 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8;
x_146 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_114);
x_147 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_112);
x_148 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_108);
x_149 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_150 = l_Lean_mkApp5(x_145, x_142, x_146, x_147, x_148, x_149);
lean_inc_ref(x_144);
x_151 = l_Lean_mkPropEq(x_111, x_144);
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
lean_dec_ref(x_114);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
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
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
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
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_168 = lean_box(0);
lean_ctor_set(x_165, 0, x_168);
return x_165;
}
else
{
uint8_t x_169; 
lean_free_object(x_165);
x_169 = !lean_is_exclusive(x_167);
if (x_169 == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_167, 0);
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; uint8_t x_173; 
x_172 = lean_ctor_get(x_170, 1);
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_ctor_get(x_170, 0);
x_175 = lean_ctor_get(x_172, 0);
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
x_177 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_177, 0, x_163);
lean_closure_set(x_177, 1, x_176);
lean_inc(x_174);
lean_inc_ref(x_177);
x_178 = l_Int_Linear_Expr_denoteExpr___redArg(x_177, x_174);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
lean_dec_ref(x_178);
lean_inc(x_175);
lean_inc_ref(x_177);
x_180 = l_Int_Linear_Expr_denoteExpr___redArg(x_177, x_175);
if (lean_obj_tag(x_180) == 0)
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_182 = lean_ctor_get(x_180, 0);
x_183 = l_Lean_mkIntLE(x_179, x_182);
lean_inc(x_175);
lean_inc(x_174);
lean_ctor_set_tag(x_170, 3);
lean_ctor_set(x_170, 1, x_175);
x_184 = l_Int_Linear_Expr_norm(x_170);
lean_dec_ref(x_170);
x_185 = l_Int_Linear_Poly_isUnsatLe(x_184);
if (x_185 == 0)
{
uint8_t x_186; 
x_186 = l_Int_Linear_Poly_isValidLe(x_184);
if (x_186 == 0)
{
lean_free_object(x_172);
lean_free_object(x_167);
if (x_164 == 0)
{
lean_free_object(x_180);
x_108 = x_184;
x_109 = x_177;
x_110 = lean_box(0);
x_111 = x_183;
x_112 = x_175;
x_113 = x_176;
x_114 = x_174;
goto block_162;
}
else
{
lean_object* x_187; uint8_t x_188; 
lean_inc_ref(x_184);
x_187 = l_Int_Linear_Poly_toExpr(x_184);
x_188 = l_Int_Linear_instBEqExpr_beq(x_187, x_174);
lean_dec_ref(x_187);
if (x_188 == 0)
{
lean_free_object(x_180);
x_108 = x_184;
x_109 = x_177;
x_110 = lean_box(0);
x_111 = x_183;
x_112 = x_175;
x_113 = x_176;
x_114 = x_174;
goto block_162;
}
else
{
lean_object* x_189; uint8_t x_190; 
x_189 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36;
x_190 = l_Int_Linear_instBEqExpr_beq(x_175, x_189);
if (x_190 == 0)
{
lean_free_object(x_180);
x_108 = x_184;
x_109 = x_177;
x_110 = lean_box(0);
x_111 = x_183;
x_112 = x_175;
x_113 = x_176;
x_114 = x_174;
goto block_162;
}
else
{
lean_object* x_191; 
lean_dec_ref(x_184);
lean_dec_ref(x_183);
lean_dec_ref(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_191 = lean_box(0);
lean_ctor_set(x_180, 0, x_191);
return x_180;
}
}
}
}
else
{
lean_object* x_192; 
lean_dec_ref(x_184);
lean_free_object(x_180);
lean_dec_ref(x_177);
x_192 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_176, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_192) == 0)
{
uint8_t x_193; 
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_194 = lean_ctor_get(x_192, 0);
x_195 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39;
x_196 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
x_197 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_174);
x_198 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_175);
x_199 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_200 = l_Lean_mkApp4(x_196, x_194, x_197, x_198, x_199);
x_201 = l_Lean_mkPropEq(x_183, x_195);
x_202 = l_Lean_Meta_mkExpectedPropHint(x_200, x_201);
lean_ctor_set(x_172, 1, x_202);
lean_ctor_set(x_172, 0, x_195);
lean_ctor_set(x_167, 0, x_172);
lean_ctor_set(x_192, 0, x_167);
return x_192;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_203 = lean_ctor_get(x_192, 0);
lean_inc(x_203);
lean_dec(x_192);
x_204 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39;
x_205 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
x_206 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_174);
x_207 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_175);
x_208 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_209 = l_Lean_mkApp4(x_205, x_203, x_206, x_207, x_208);
x_210 = l_Lean_mkPropEq(x_183, x_204);
x_211 = l_Lean_Meta_mkExpectedPropHint(x_209, x_210);
lean_ctor_set(x_172, 1, x_211);
lean_ctor_set(x_172, 0, x_204);
lean_ctor_set(x_167, 0, x_172);
x_212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_212, 0, x_167);
return x_212;
}
}
else
{
uint8_t x_213; 
lean_dec_ref(x_183);
lean_free_object(x_172);
lean_dec(x_175);
lean_dec(x_174);
lean_free_object(x_167);
x_213 = !lean_is_exclusive(x_192);
if (x_213 == 0)
{
return x_192;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_192, 0);
lean_inc(x_214);
lean_dec(x_192);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
return x_215;
}
}
}
}
else
{
lean_object* x_216; 
lean_dec_ref(x_184);
lean_free_object(x_180);
lean_dec_ref(x_177);
x_216 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_176, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_216) == 0)
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_218 = lean_ctor_get(x_216, 0);
x_219 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9;
x_220 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
x_221 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_174);
x_222 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_175);
x_223 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_224 = l_Lean_mkApp4(x_220, x_218, x_221, x_222, x_223);
x_225 = l_Lean_mkPropEq(x_183, x_219);
x_226 = l_Lean_Meta_mkExpectedPropHint(x_224, x_225);
lean_ctor_set(x_172, 1, x_226);
lean_ctor_set(x_172, 0, x_219);
lean_ctor_set(x_167, 0, x_172);
lean_ctor_set(x_216, 0, x_167);
return x_216;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_227 = lean_ctor_get(x_216, 0);
lean_inc(x_227);
lean_dec(x_216);
x_228 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9;
x_229 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
x_230 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_174);
x_231 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_175);
x_232 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_233 = l_Lean_mkApp4(x_229, x_227, x_230, x_231, x_232);
x_234 = l_Lean_mkPropEq(x_183, x_228);
x_235 = l_Lean_Meta_mkExpectedPropHint(x_233, x_234);
lean_ctor_set(x_172, 1, x_235);
lean_ctor_set(x_172, 0, x_228);
lean_ctor_set(x_167, 0, x_172);
x_236 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_236, 0, x_167);
return x_236;
}
}
else
{
uint8_t x_237; 
lean_dec_ref(x_183);
lean_free_object(x_172);
lean_dec(x_175);
lean_dec(x_174);
lean_free_object(x_167);
x_237 = !lean_is_exclusive(x_216);
if (x_237 == 0)
{
return x_216;
}
else
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_216, 0);
lean_inc(x_238);
lean_dec(x_216);
x_239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_239, 0, x_238);
return x_239;
}
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_240 = lean_ctor_get(x_180, 0);
lean_inc(x_240);
lean_dec(x_180);
x_241 = l_Lean_mkIntLE(x_179, x_240);
lean_inc(x_175);
lean_inc(x_174);
lean_ctor_set_tag(x_170, 3);
lean_ctor_set(x_170, 1, x_175);
x_242 = l_Int_Linear_Expr_norm(x_170);
lean_dec_ref(x_170);
x_243 = l_Int_Linear_Poly_isUnsatLe(x_242);
if (x_243 == 0)
{
uint8_t x_244; 
x_244 = l_Int_Linear_Poly_isValidLe(x_242);
if (x_244 == 0)
{
lean_free_object(x_172);
lean_free_object(x_167);
if (x_164 == 0)
{
x_108 = x_242;
x_109 = x_177;
x_110 = lean_box(0);
x_111 = x_241;
x_112 = x_175;
x_113 = x_176;
x_114 = x_174;
goto block_162;
}
else
{
lean_object* x_245; uint8_t x_246; 
lean_inc_ref(x_242);
x_245 = l_Int_Linear_Poly_toExpr(x_242);
x_246 = l_Int_Linear_instBEqExpr_beq(x_245, x_174);
lean_dec_ref(x_245);
if (x_246 == 0)
{
x_108 = x_242;
x_109 = x_177;
x_110 = lean_box(0);
x_111 = x_241;
x_112 = x_175;
x_113 = x_176;
x_114 = x_174;
goto block_162;
}
else
{
lean_object* x_247; uint8_t x_248; 
x_247 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36;
x_248 = l_Int_Linear_instBEqExpr_beq(x_175, x_247);
if (x_248 == 0)
{
x_108 = x_242;
x_109 = x_177;
x_110 = lean_box(0);
x_111 = x_241;
x_112 = x_175;
x_113 = x_176;
x_114 = x_174;
goto block_162;
}
else
{
lean_object* x_249; lean_object* x_250; 
lean_dec_ref(x_242);
lean_dec_ref(x_241);
lean_dec_ref(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_249 = lean_box(0);
x_250 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_250, 0, x_249);
return x_250;
}
}
}
}
else
{
lean_object* x_251; 
lean_dec_ref(x_242);
lean_dec_ref(x_177);
x_251 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_176, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 x_253 = x_251;
} else {
 lean_dec_ref(x_251);
 x_253 = lean_box(0);
}
x_254 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39;
x_255 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
x_256 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_174);
x_257 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_175);
x_258 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_259 = l_Lean_mkApp4(x_255, x_252, x_256, x_257, x_258);
x_260 = l_Lean_mkPropEq(x_241, x_254);
x_261 = l_Lean_Meta_mkExpectedPropHint(x_259, x_260);
lean_ctor_set(x_172, 1, x_261);
lean_ctor_set(x_172, 0, x_254);
lean_ctor_set(x_167, 0, x_172);
if (lean_is_scalar(x_253)) {
 x_262 = lean_alloc_ctor(0, 1, 0);
} else {
 x_262 = x_253;
}
lean_ctor_set(x_262, 0, x_167);
return x_262;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec_ref(x_241);
lean_free_object(x_172);
lean_dec(x_175);
lean_dec(x_174);
lean_free_object(x_167);
x_263 = lean_ctor_get(x_251, 0);
lean_inc(x_263);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 x_264 = x_251;
} else {
 lean_dec_ref(x_251);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(1, 1, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_263);
return x_265;
}
}
}
else
{
lean_object* x_266; 
lean_dec_ref(x_242);
lean_dec_ref(x_177);
x_266 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_176, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 x_268 = x_266;
} else {
 lean_dec_ref(x_266);
 x_268 = lean_box(0);
}
x_269 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9;
x_270 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
x_271 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_174);
x_272 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_175);
x_273 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_274 = l_Lean_mkApp4(x_270, x_267, x_271, x_272, x_273);
x_275 = l_Lean_mkPropEq(x_241, x_269);
x_276 = l_Lean_Meta_mkExpectedPropHint(x_274, x_275);
lean_ctor_set(x_172, 1, x_276);
lean_ctor_set(x_172, 0, x_269);
lean_ctor_set(x_167, 0, x_172);
if (lean_is_scalar(x_268)) {
 x_277 = lean_alloc_ctor(0, 1, 0);
} else {
 x_277 = x_268;
}
lean_ctor_set(x_277, 0, x_167);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec_ref(x_241);
lean_free_object(x_172);
lean_dec(x_175);
lean_dec(x_174);
lean_free_object(x_167);
x_278 = lean_ctor_get(x_266, 0);
lean_inc(x_278);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 x_279 = x_266;
} else {
 lean_dec_ref(x_266);
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
}
}
else
{
uint8_t x_281; 
lean_dec(x_179);
lean_dec_ref(x_177);
lean_free_object(x_172);
lean_dec(x_176);
lean_dec(x_175);
lean_free_object(x_170);
lean_dec(x_174);
lean_free_object(x_167);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_281 = !lean_is_exclusive(x_180);
if (x_281 == 0)
{
return x_180;
}
else
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_180, 0);
lean_inc(x_282);
lean_dec(x_180);
x_283 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_283, 0, x_282);
return x_283;
}
}
}
else
{
uint8_t x_284; 
lean_dec_ref(x_177);
lean_free_object(x_172);
lean_dec(x_176);
lean_dec(x_175);
lean_free_object(x_170);
lean_dec(x_174);
lean_free_object(x_167);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_284 = !lean_is_exclusive(x_178);
if (x_284 == 0)
{
return x_178;
}
else
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_178, 0);
lean_inc(x_285);
lean_dec(x_178);
x_286 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_286, 0, x_285);
return x_286;
}
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_287 = lean_ctor_get(x_170, 0);
x_288 = lean_ctor_get(x_172, 0);
x_289 = lean_ctor_get(x_172, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_172);
lean_inc(x_289);
x_290 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_290, 0, x_163);
lean_closure_set(x_290, 1, x_289);
lean_inc(x_287);
lean_inc_ref(x_290);
x_291 = l_Int_Linear_Expr_denoteExpr___redArg(x_290, x_287);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
lean_dec_ref(x_291);
lean_inc(x_288);
lean_inc_ref(x_290);
x_293 = l_Int_Linear_Expr_denoteExpr___redArg(x_290, x_288);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 x_295 = x_293;
} else {
 lean_dec_ref(x_293);
 x_295 = lean_box(0);
}
x_296 = l_Lean_mkIntLE(x_292, x_294);
lean_inc(x_288);
lean_inc(x_287);
lean_ctor_set_tag(x_170, 3);
lean_ctor_set(x_170, 1, x_288);
x_297 = l_Int_Linear_Expr_norm(x_170);
lean_dec_ref(x_170);
x_298 = l_Int_Linear_Poly_isUnsatLe(x_297);
if (x_298 == 0)
{
uint8_t x_299; 
x_299 = l_Int_Linear_Poly_isValidLe(x_297);
if (x_299 == 0)
{
lean_free_object(x_167);
if (x_164 == 0)
{
lean_dec(x_295);
x_108 = x_297;
x_109 = x_290;
x_110 = lean_box(0);
x_111 = x_296;
x_112 = x_288;
x_113 = x_289;
x_114 = x_287;
goto block_162;
}
else
{
lean_object* x_300; uint8_t x_301; 
lean_inc_ref(x_297);
x_300 = l_Int_Linear_Poly_toExpr(x_297);
x_301 = l_Int_Linear_instBEqExpr_beq(x_300, x_287);
lean_dec_ref(x_300);
if (x_301 == 0)
{
lean_dec(x_295);
x_108 = x_297;
x_109 = x_290;
x_110 = lean_box(0);
x_111 = x_296;
x_112 = x_288;
x_113 = x_289;
x_114 = x_287;
goto block_162;
}
else
{
lean_object* x_302; uint8_t x_303; 
x_302 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36;
x_303 = l_Int_Linear_instBEqExpr_beq(x_288, x_302);
if (x_303 == 0)
{
lean_dec(x_295);
x_108 = x_297;
x_109 = x_290;
x_110 = lean_box(0);
x_111 = x_296;
x_112 = x_288;
x_113 = x_289;
x_114 = x_287;
goto block_162;
}
else
{
lean_object* x_304; lean_object* x_305; 
lean_dec_ref(x_297);
lean_dec_ref(x_296);
lean_dec_ref(x_290);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_304 = lean_box(0);
if (lean_is_scalar(x_295)) {
 x_305 = lean_alloc_ctor(0, 1, 0);
} else {
 x_305 = x_295;
}
lean_ctor_set(x_305, 0, x_304);
return x_305;
}
}
}
}
else
{
lean_object* x_306; 
lean_dec_ref(x_297);
lean_dec(x_295);
lean_dec_ref(x_290);
x_306 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_289, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 x_308 = x_306;
} else {
 lean_dec_ref(x_306);
 x_308 = lean_box(0);
}
x_309 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39;
x_310 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
x_311 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_287);
x_312 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_288);
x_313 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_314 = l_Lean_mkApp4(x_310, x_307, x_311, x_312, x_313);
x_315 = l_Lean_mkPropEq(x_296, x_309);
x_316 = l_Lean_Meta_mkExpectedPropHint(x_314, x_315);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_316);
lean_ctor_set(x_167, 0, x_317);
if (lean_is_scalar(x_308)) {
 x_318 = lean_alloc_ctor(0, 1, 0);
} else {
 x_318 = x_308;
}
lean_ctor_set(x_318, 0, x_167);
return x_318;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec_ref(x_296);
lean_dec(x_288);
lean_dec(x_287);
lean_free_object(x_167);
x_319 = lean_ctor_get(x_306, 0);
lean_inc(x_319);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 x_320 = x_306;
} else {
 lean_dec_ref(x_306);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 1, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_319);
return x_321;
}
}
}
else
{
lean_object* x_322; 
lean_dec_ref(x_297);
lean_dec(x_295);
lean_dec_ref(x_290);
x_322 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_289, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 x_324 = x_322;
} else {
 lean_dec_ref(x_322);
 x_324 = lean_box(0);
}
x_325 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9;
x_326 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
x_327 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_287);
x_328 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_288);
x_329 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_330 = l_Lean_mkApp4(x_326, x_323, x_327, x_328, x_329);
x_331 = l_Lean_mkPropEq(x_296, x_325);
x_332 = l_Lean_Meta_mkExpectedPropHint(x_330, x_331);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_325);
lean_ctor_set(x_333, 1, x_332);
lean_ctor_set(x_167, 0, x_333);
if (lean_is_scalar(x_324)) {
 x_334 = lean_alloc_ctor(0, 1, 0);
} else {
 x_334 = x_324;
}
lean_ctor_set(x_334, 0, x_167);
return x_334;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec_ref(x_296);
lean_dec(x_288);
lean_dec(x_287);
lean_free_object(x_167);
x_335 = lean_ctor_get(x_322, 0);
lean_inc(x_335);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 x_336 = x_322;
} else {
 lean_dec_ref(x_322);
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
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_292);
lean_dec_ref(x_290);
lean_dec(x_289);
lean_dec(x_288);
lean_free_object(x_170);
lean_dec(x_287);
lean_free_object(x_167);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_338 = lean_ctor_get(x_293, 0);
lean_inc(x_338);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 x_339 = x_293;
} else {
 lean_dec_ref(x_293);
 x_339 = lean_box(0);
}
if (lean_is_scalar(x_339)) {
 x_340 = lean_alloc_ctor(1, 1, 0);
} else {
 x_340 = x_339;
}
lean_ctor_set(x_340, 0, x_338);
return x_340;
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec_ref(x_290);
lean_dec(x_289);
lean_dec(x_288);
lean_free_object(x_170);
lean_dec(x_287);
lean_free_object(x_167);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_341 = lean_ctor_get(x_291, 0);
lean_inc(x_341);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_342 = x_291;
} else {
 lean_dec_ref(x_291);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(1, 1, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_341);
return x_343;
}
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_344 = lean_ctor_get(x_170, 1);
x_345 = lean_ctor_get(x_170, 0);
lean_inc(x_344);
lean_inc(x_345);
lean_dec(x_170);
x_346 = lean_ctor_get(x_344, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_344, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_348 = x_344;
} else {
 lean_dec_ref(x_344);
 x_348 = lean_box(0);
}
lean_inc(x_347);
x_349 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_349, 0, x_163);
lean_closure_set(x_349, 1, x_347);
lean_inc(x_345);
lean_inc_ref(x_349);
x_350 = l_Int_Linear_Expr_denoteExpr___redArg(x_349, x_345);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
lean_dec_ref(x_350);
lean_inc(x_346);
lean_inc_ref(x_349);
x_352 = l_Int_Linear_Expr_denoteExpr___redArg(x_349, x_346);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 x_354 = x_352;
} else {
 lean_dec_ref(x_352);
 x_354 = lean_box(0);
}
x_355 = l_Lean_mkIntLE(x_351, x_353);
lean_inc(x_346);
lean_inc(x_345);
x_356 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_356, 0, x_345);
lean_ctor_set(x_356, 1, x_346);
x_357 = l_Int_Linear_Expr_norm(x_356);
lean_dec_ref(x_356);
x_358 = l_Int_Linear_Poly_isUnsatLe(x_357);
if (x_358 == 0)
{
uint8_t x_359; 
x_359 = l_Int_Linear_Poly_isValidLe(x_357);
if (x_359 == 0)
{
lean_dec(x_348);
lean_free_object(x_167);
if (x_164 == 0)
{
lean_dec(x_354);
x_108 = x_357;
x_109 = x_349;
x_110 = lean_box(0);
x_111 = x_355;
x_112 = x_346;
x_113 = x_347;
x_114 = x_345;
goto block_162;
}
else
{
lean_object* x_360; uint8_t x_361; 
lean_inc_ref(x_357);
x_360 = l_Int_Linear_Poly_toExpr(x_357);
x_361 = l_Int_Linear_instBEqExpr_beq(x_360, x_345);
lean_dec_ref(x_360);
if (x_361 == 0)
{
lean_dec(x_354);
x_108 = x_357;
x_109 = x_349;
x_110 = lean_box(0);
x_111 = x_355;
x_112 = x_346;
x_113 = x_347;
x_114 = x_345;
goto block_162;
}
else
{
lean_object* x_362; uint8_t x_363; 
x_362 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36;
x_363 = l_Int_Linear_instBEqExpr_beq(x_346, x_362);
if (x_363 == 0)
{
lean_dec(x_354);
x_108 = x_357;
x_109 = x_349;
x_110 = lean_box(0);
x_111 = x_355;
x_112 = x_346;
x_113 = x_347;
x_114 = x_345;
goto block_162;
}
else
{
lean_object* x_364; lean_object* x_365; 
lean_dec_ref(x_357);
lean_dec_ref(x_355);
lean_dec_ref(x_349);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_364 = lean_box(0);
if (lean_is_scalar(x_354)) {
 x_365 = lean_alloc_ctor(0, 1, 0);
} else {
 x_365 = x_354;
}
lean_ctor_set(x_365, 0, x_364);
return x_365;
}
}
}
}
else
{
lean_object* x_366; 
lean_dec_ref(x_357);
lean_dec(x_354);
lean_dec_ref(x_349);
x_366 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_347, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 x_368 = x_366;
} else {
 lean_dec_ref(x_366);
 x_368 = lean_box(0);
}
x_369 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39;
x_370 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
x_371 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_345);
x_372 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_346);
x_373 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_374 = l_Lean_mkApp4(x_370, x_367, x_371, x_372, x_373);
x_375 = l_Lean_mkPropEq(x_355, x_369);
x_376 = l_Lean_Meta_mkExpectedPropHint(x_374, x_375);
if (lean_is_scalar(x_348)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_348;
}
lean_ctor_set(x_377, 0, x_369);
lean_ctor_set(x_377, 1, x_376);
lean_ctor_set(x_167, 0, x_377);
if (lean_is_scalar(x_368)) {
 x_378 = lean_alloc_ctor(0, 1, 0);
} else {
 x_378 = x_368;
}
lean_ctor_set(x_378, 0, x_167);
return x_378;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec_ref(x_355);
lean_dec(x_348);
lean_dec(x_346);
lean_dec(x_345);
lean_free_object(x_167);
x_379 = lean_ctor_get(x_366, 0);
lean_inc(x_379);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 x_380 = x_366;
} else {
 lean_dec_ref(x_366);
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
}
else
{
lean_object* x_382; 
lean_dec_ref(x_357);
lean_dec(x_354);
lean_dec_ref(x_349);
x_382 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_347, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 x_384 = x_382;
} else {
 lean_dec_ref(x_382);
 x_384 = lean_box(0);
}
x_385 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9;
x_386 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
x_387 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_345);
x_388 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_346);
x_389 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_390 = l_Lean_mkApp4(x_386, x_383, x_387, x_388, x_389);
x_391 = l_Lean_mkPropEq(x_355, x_385);
x_392 = l_Lean_Meta_mkExpectedPropHint(x_390, x_391);
if (lean_is_scalar(x_348)) {
 x_393 = lean_alloc_ctor(0, 2, 0);
} else {
 x_393 = x_348;
}
lean_ctor_set(x_393, 0, x_385);
lean_ctor_set(x_393, 1, x_392);
lean_ctor_set(x_167, 0, x_393);
if (lean_is_scalar(x_384)) {
 x_394 = lean_alloc_ctor(0, 1, 0);
} else {
 x_394 = x_384;
}
lean_ctor_set(x_394, 0, x_167);
return x_394;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec_ref(x_355);
lean_dec(x_348);
lean_dec(x_346);
lean_dec(x_345);
lean_free_object(x_167);
x_395 = lean_ctor_get(x_382, 0);
lean_inc(x_395);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 x_396 = x_382;
} else {
 lean_dec_ref(x_382);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 1, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_395);
return x_397;
}
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_351);
lean_dec_ref(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_free_object(x_167);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_398 = lean_ctor_get(x_352, 0);
lean_inc(x_398);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 x_399 = x_352;
} else {
 lean_dec_ref(x_352);
 x_399 = lean_box(0);
}
if (lean_is_scalar(x_399)) {
 x_400 = lean_alloc_ctor(1, 1, 0);
} else {
 x_400 = x_399;
}
lean_ctor_set(x_400, 0, x_398);
return x_400;
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec_ref(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_free_object(x_167);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_401 = lean_ctor_get(x_350, 0);
lean_inc(x_401);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 x_402 = x_350;
} else {
 lean_dec_ref(x_350);
 x_402 = lean_box(0);
}
if (lean_is_scalar(x_402)) {
 x_403 = lean_alloc_ctor(1, 1, 0);
} else {
 x_403 = x_402;
}
lean_ctor_set(x_403, 0, x_401);
return x_403;
}
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_404 = lean_ctor_get(x_167, 0);
lean_inc(x_404);
lean_dec(x_167);
x_405 = lean_ctor_get(x_404, 1);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 0);
lean_inc(x_406);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_407 = x_404;
} else {
 lean_dec_ref(x_404);
 x_407 = lean_box(0);
}
x_408 = lean_ctor_get(x_405, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_405, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 x_410 = x_405;
} else {
 lean_dec_ref(x_405);
 x_410 = lean_box(0);
}
lean_inc(x_409);
x_411 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_411, 0, x_163);
lean_closure_set(x_411, 1, x_409);
lean_inc(x_406);
lean_inc_ref(x_411);
x_412 = l_Int_Linear_Expr_denoteExpr___redArg(x_411, x_406);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
lean_dec_ref(x_412);
lean_inc(x_408);
lean_inc_ref(x_411);
x_414 = l_Int_Linear_Expr_denoteExpr___redArg(x_411, x_408);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 x_416 = x_414;
} else {
 lean_dec_ref(x_414);
 x_416 = lean_box(0);
}
x_417 = l_Lean_mkIntLE(x_413, x_415);
lean_inc(x_408);
lean_inc(x_406);
if (lean_is_scalar(x_407)) {
 x_418 = lean_alloc_ctor(3, 2, 0);
} else {
 x_418 = x_407;
 lean_ctor_set_tag(x_418, 3);
}
lean_ctor_set(x_418, 0, x_406);
lean_ctor_set(x_418, 1, x_408);
x_419 = l_Int_Linear_Expr_norm(x_418);
lean_dec_ref(x_418);
x_420 = l_Int_Linear_Poly_isUnsatLe(x_419);
if (x_420 == 0)
{
uint8_t x_421; 
x_421 = l_Int_Linear_Poly_isValidLe(x_419);
if (x_421 == 0)
{
lean_dec(x_410);
if (x_164 == 0)
{
lean_dec(x_416);
x_108 = x_419;
x_109 = x_411;
x_110 = lean_box(0);
x_111 = x_417;
x_112 = x_408;
x_113 = x_409;
x_114 = x_406;
goto block_162;
}
else
{
lean_object* x_422; uint8_t x_423; 
lean_inc_ref(x_419);
x_422 = l_Int_Linear_Poly_toExpr(x_419);
x_423 = l_Int_Linear_instBEqExpr_beq(x_422, x_406);
lean_dec_ref(x_422);
if (x_423 == 0)
{
lean_dec(x_416);
x_108 = x_419;
x_109 = x_411;
x_110 = lean_box(0);
x_111 = x_417;
x_112 = x_408;
x_113 = x_409;
x_114 = x_406;
goto block_162;
}
else
{
lean_object* x_424; uint8_t x_425; 
x_424 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36;
x_425 = l_Int_Linear_instBEqExpr_beq(x_408, x_424);
if (x_425 == 0)
{
lean_dec(x_416);
x_108 = x_419;
x_109 = x_411;
x_110 = lean_box(0);
x_111 = x_417;
x_112 = x_408;
x_113 = x_409;
x_114 = x_406;
goto block_162;
}
else
{
lean_object* x_426; lean_object* x_427; 
lean_dec_ref(x_419);
lean_dec_ref(x_417);
lean_dec_ref(x_411);
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_406);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_426 = lean_box(0);
if (lean_is_scalar(x_416)) {
 x_427 = lean_alloc_ctor(0, 1, 0);
} else {
 x_427 = x_416;
}
lean_ctor_set(x_427, 0, x_426);
return x_427;
}
}
}
}
else
{
lean_object* x_428; 
lean_dec_ref(x_419);
lean_dec(x_416);
lean_dec_ref(x_411);
x_428 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_409, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 x_430 = x_428;
} else {
 lean_dec_ref(x_428);
 x_430 = lean_box(0);
}
x_431 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39;
x_432 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
x_433 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_406);
x_434 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_408);
x_435 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_436 = l_Lean_mkApp4(x_432, x_429, x_433, x_434, x_435);
x_437 = l_Lean_mkPropEq(x_417, x_431);
x_438 = l_Lean_Meta_mkExpectedPropHint(x_436, x_437);
if (lean_is_scalar(x_410)) {
 x_439 = lean_alloc_ctor(0, 2, 0);
} else {
 x_439 = x_410;
}
lean_ctor_set(x_439, 0, x_431);
lean_ctor_set(x_439, 1, x_438);
x_440 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_440, 0, x_439);
if (lean_is_scalar(x_430)) {
 x_441 = lean_alloc_ctor(0, 1, 0);
} else {
 x_441 = x_430;
}
lean_ctor_set(x_441, 0, x_440);
return x_441;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec_ref(x_417);
lean_dec(x_410);
lean_dec(x_408);
lean_dec(x_406);
x_442 = lean_ctor_get(x_428, 0);
lean_inc(x_442);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 x_443 = x_428;
} else {
 lean_dec_ref(x_428);
 x_443 = lean_box(0);
}
if (lean_is_scalar(x_443)) {
 x_444 = lean_alloc_ctor(1, 1, 0);
} else {
 x_444 = x_443;
}
lean_ctor_set(x_444, 0, x_442);
return x_444;
}
}
}
else
{
lean_object* x_445; 
lean_dec_ref(x_419);
lean_dec(x_416);
lean_dec_ref(x_411);
x_445 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_409, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 x_447 = x_445;
} else {
 lean_dec_ref(x_445);
 x_447 = lean_box(0);
}
x_448 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9;
x_449 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
x_450 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_406);
x_451 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_408);
x_452 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_453 = l_Lean_mkApp4(x_449, x_446, x_450, x_451, x_452);
x_454 = l_Lean_mkPropEq(x_417, x_448);
x_455 = l_Lean_Meta_mkExpectedPropHint(x_453, x_454);
if (lean_is_scalar(x_410)) {
 x_456 = lean_alloc_ctor(0, 2, 0);
} else {
 x_456 = x_410;
}
lean_ctor_set(x_456, 0, x_448);
lean_ctor_set(x_456, 1, x_455);
x_457 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_457, 0, x_456);
if (lean_is_scalar(x_447)) {
 x_458 = lean_alloc_ctor(0, 1, 0);
} else {
 x_458 = x_447;
}
lean_ctor_set(x_458, 0, x_457);
return x_458;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec_ref(x_417);
lean_dec(x_410);
lean_dec(x_408);
lean_dec(x_406);
x_459 = lean_ctor_get(x_445, 0);
lean_inc(x_459);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 x_460 = x_445;
} else {
 lean_dec_ref(x_445);
 x_460 = lean_box(0);
}
if (lean_is_scalar(x_460)) {
 x_461 = lean_alloc_ctor(1, 1, 0);
} else {
 x_461 = x_460;
}
lean_ctor_set(x_461, 0, x_459);
return x_461;
}
}
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_dec(x_413);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_462 = lean_ctor_get(x_414, 0);
lean_inc(x_462);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 x_463 = x_414;
} else {
 lean_dec_ref(x_414);
 x_463 = lean_box(0);
}
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(1, 1, 0);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_462);
return x_464;
}
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_465 = lean_ctor_get(x_412, 0);
lean_inc(x_465);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 x_466 = x_412;
} else {
 lean_dec_ref(x_412);
 x_466 = lean_box(0);
}
if (lean_is_scalar(x_466)) {
 x_467 = lean_alloc_ctor(1, 1, 0);
} else {
 x_467 = x_466;
}
lean_ctor_set(x_467, 0, x_465);
return x_467;
}
}
}
}
else
{
lean_object* x_468; 
x_468 = lean_ctor_get(x_165, 0);
lean_inc(x_468);
lean_dec(x_165);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; lean_object* x_470; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_469 = lean_box(0);
x_470 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_470, 0, x_469);
return x_470;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_471 = lean_ctor_get(x_468, 0);
lean_inc(x_471);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 x_472 = x_468;
} else {
 lean_dec_ref(x_468);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_471, 1);
lean_inc(x_473);
x_474 = lean_ctor_get(x_471, 0);
lean_inc(x_474);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 lean_ctor_release(x_471, 1);
 x_475 = x_471;
} else {
 lean_dec_ref(x_471);
 x_475 = lean_box(0);
}
x_476 = lean_ctor_get(x_473, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_473, 1);
lean_inc(x_477);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_478 = x_473;
} else {
 lean_dec_ref(x_473);
 x_478 = lean_box(0);
}
lean_inc(x_477);
x_479 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_479, 0, x_163);
lean_closure_set(x_479, 1, x_477);
lean_inc(x_474);
lean_inc_ref(x_479);
x_480 = l_Int_Linear_Expr_denoteExpr___redArg(x_479, x_474);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
lean_dec_ref(x_480);
lean_inc(x_476);
lean_inc_ref(x_479);
x_482 = l_Int_Linear_Expr_denoteExpr___redArg(x_479, x_476);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 x_484 = x_482;
} else {
 lean_dec_ref(x_482);
 x_484 = lean_box(0);
}
x_485 = l_Lean_mkIntLE(x_481, x_483);
lean_inc(x_476);
lean_inc(x_474);
if (lean_is_scalar(x_475)) {
 x_486 = lean_alloc_ctor(3, 2, 0);
} else {
 x_486 = x_475;
 lean_ctor_set_tag(x_486, 3);
}
lean_ctor_set(x_486, 0, x_474);
lean_ctor_set(x_486, 1, x_476);
x_487 = l_Int_Linear_Expr_norm(x_486);
lean_dec_ref(x_486);
x_488 = l_Int_Linear_Poly_isUnsatLe(x_487);
if (x_488 == 0)
{
uint8_t x_489; 
x_489 = l_Int_Linear_Poly_isValidLe(x_487);
if (x_489 == 0)
{
lean_dec(x_478);
lean_dec(x_472);
if (x_164 == 0)
{
lean_dec(x_484);
x_108 = x_487;
x_109 = x_479;
x_110 = lean_box(0);
x_111 = x_485;
x_112 = x_476;
x_113 = x_477;
x_114 = x_474;
goto block_162;
}
else
{
lean_object* x_490; uint8_t x_491; 
lean_inc_ref(x_487);
x_490 = l_Int_Linear_Poly_toExpr(x_487);
x_491 = l_Int_Linear_instBEqExpr_beq(x_490, x_474);
lean_dec_ref(x_490);
if (x_491 == 0)
{
lean_dec(x_484);
x_108 = x_487;
x_109 = x_479;
x_110 = lean_box(0);
x_111 = x_485;
x_112 = x_476;
x_113 = x_477;
x_114 = x_474;
goto block_162;
}
else
{
lean_object* x_492; uint8_t x_493; 
x_492 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36;
x_493 = l_Int_Linear_instBEqExpr_beq(x_476, x_492);
if (x_493 == 0)
{
lean_dec(x_484);
x_108 = x_487;
x_109 = x_479;
x_110 = lean_box(0);
x_111 = x_485;
x_112 = x_476;
x_113 = x_477;
x_114 = x_474;
goto block_162;
}
else
{
lean_object* x_494; lean_object* x_495; 
lean_dec_ref(x_487);
lean_dec_ref(x_485);
lean_dec_ref(x_479);
lean_dec(x_477);
lean_dec(x_476);
lean_dec(x_474);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_494 = lean_box(0);
if (lean_is_scalar(x_484)) {
 x_495 = lean_alloc_ctor(0, 1, 0);
} else {
 x_495 = x_484;
}
lean_ctor_set(x_495, 0, x_494);
return x_495;
}
}
}
}
else
{
lean_object* x_496; 
lean_dec_ref(x_487);
lean_dec(x_484);
lean_dec_ref(x_479);
x_496 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_477, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 x_498 = x_496;
} else {
 lean_dec_ref(x_496);
 x_498 = lean_box(0);
}
x_499 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39;
x_500 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
x_501 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_474);
x_502 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_476);
x_503 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_504 = l_Lean_mkApp4(x_500, x_497, x_501, x_502, x_503);
x_505 = l_Lean_mkPropEq(x_485, x_499);
x_506 = l_Lean_Meta_mkExpectedPropHint(x_504, x_505);
if (lean_is_scalar(x_478)) {
 x_507 = lean_alloc_ctor(0, 2, 0);
} else {
 x_507 = x_478;
}
lean_ctor_set(x_507, 0, x_499);
lean_ctor_set(x_507, 1, x_506);
if (lean_is_scalar(x_472)) {
 x_508 = lean_alloc_ctor(1, 1, 0);
} else {
 x_508 = x_472;
}
lean_ctor_set(x_508, 0, x_507);
if (lean_is_scalar(x_498)) {
 x_509 = lean_alloc_ctor(0, 1, 0);
} else {
 x_509 = x_498;
}
lean_ctor_set(x_509, 0, x_508);
return x_509;
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec_ref(x_485);
lean_dec(x_478);
lean_dec(x_476);
lean_dec(x_474);
lean_dec(x_472);
x_510 = lean_ctor_get(x_496, 0);
lean_inc(x_510);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 x_511 = x_496;
} else {
 lean_dec_ref(x_496);
 x_511 = lean_box(0);
}
if (lean_is_scalar(x_511)) {
 x_512 = lean_alloc_ctor(1, 1, 0);
} else {
 x_512 = x_511;
}
lean_ctor_set(x_512, 0, x_510);
return x_512;
}
}
}
else
{
lean_object* x_513; 
lean_dec_ref(x_487);
lean_dec(x_484);
lean_dec_ref(x_479);
x_513 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_477, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 x_515 = x_513;
} else {
 lean_dec_ref(x_513);
 x_515 = lean_box(0);
}
x_516 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9;
x_517 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
x_518 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_474);
x_519 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_476);
x_520 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_521 = l_Lean_mkApp4(x_517, x_514, x_518, x_519, x_520);
x_522 = l_Lean_mkPropEq(x_485, x_516);
x_523 = l_Lean_Meta_mkExpectedPropHint(x_521, x_522);
if (lean_is_scalar(x_478)) {
 x_524 = lean_alloc_ctor(0, 2, 0);
} else {
 x_524 = x_478;
}
lean_ctor_set(x_524, 0, x_516);
lean_ctor_set(x_524, 1, x_523);
if (lean_is_scalar(x_472)) {
 x_525 = lean_alloc_ctor(1, 1, 0);
} else {
 x_525 = x_472;
}
lean_ctor_set(x_525, 0, x_524);
if (lean_is_scalar(x_515)) {
 x_526 = lean_alloc_ctor(0, 1, 0);
} else {
 x_526 = x_515;
}
lean_ctor_set(x_526, 0, x_525);
return x_526;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
lean_dec_ref(x_485);
lean_dec(x_478);
lean_dec(x_476);
lean_dec(x_474);
lean_dec(x_472);
x_527 = lean_ctor_get(x_513, 0);
lean_inc(x_527);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 x_528 = x_513;
} else {
 lean_dec_ref(x_513);
 x_528 = lean_box(0);
}
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(1, 1, 0);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_527);
return x_529;
}
}
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
lean_dec(x_481);
lean_dec_ref(x_479);
lean_dec(x_478);
lean_dec(x_477);
lean_dec(x_476);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_472);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_530 = lean_ctor_get(x_482, 0);
lean_inc(x_530);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 x_531 = x_482;
} else {
 lean_dec_ref(x_482);
 x_531 = lean_box(0);
}
if (lean_is_scalar(x_531)) {
 x_532 = lean_alloc_ctor(1, 1, 0);
} else {
 x_532 = x_531;
}
lean_ctor_set(x_532, 0, x_530);
return x_532;
}
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec_ref(x_479);
lean_dec(x_478);
lean_dec(x_477);
lean_dec(x_476);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_472);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_533 = lean_ctor_get(x_480, 0);
lean_inc(x_533);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 x_534 = x_480;
} else {
 lean_dec_ref(x_480);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(1, 1, 0);
} else {
 x_535 = x_534;
}
lean_ctor_set(x_535, 0, x_533);
return x_535;
}
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
lean_object* x_1; 
x_1 = l_Lean_levelOne;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ge", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31;
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_le_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_ge_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_lt_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_gt_eq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28;
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8;
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
lean_object* x_73; uint8_t x_74; 
lean_inc_ref(x_71);
x_73 = l_Lean_Expr_appFnCleanup___redArg(x_71);
x_74 = l_Lean_Expr_isApp(x_73);
if (x_74 == 0)
{
lean_dec_ref(x_73);
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
lean_object* x_75; uint8_t x_76; 
lean_inc_ref(x_73);
x_75 = l_Lean_Expr_appFnCleanup___redArg(x_73);
x_76 = l_Lean_Expr_isApp(x_75);
if (x_76 == 0)
{
lean_dec_ref(x_75);
lean_dec_ref(x_73);
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
lean_object* x_77; uint8_t x_78; 
x_77 = l_Lean_Expr_appFnCleanup___redArg(x_75);
x_78 = l_Lean_Expr_isApp(x_77);
if (x_78 == 0)
{
lean_dec_ref(x_77);
lean_dec_ref(x_73);
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
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_79 = lean_ctor_get(x_71, 1);
lean_inc_ref(x_79);
lean_dec_ref(x_71);
x_80 = lean_ctor_get(x_73, 1);
lean_inc_ref(x_80);
lean_dec_ref(x_73);
x_81 = lean_ctor_get(x_77, 1);
lean_inc_ref(x_81);
x_82 = l_Lean_Expr_appFnCleanup___redArg(x_77);
x_83 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11;
x_84 = l_Lean_Expr_isConstOf(x_82, x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14;
x_86 = l_Lean_Expr_isConstOf(x_82, x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17;
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
lean_dec_ref(x_80);
lean_dec_ref(x_79);
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
x_94 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
x_95 = l_Lean_Expr_isConstOf(x_93, x_94);
lean_dec_ref(x_93);
if (x_95 == 0)
{
lean_dec_ref(x_80);
lean_dec_ref(x_79);
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
x_96 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18;
lean_inc_ref(x_79);
x_97 = l_Lean_mkIntAdd(x_79, x_96);
lean_inc_ref(x_80);
x_98 = l_Lean_mkIntLE(x_97, x_80);
x_99 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21;
x_100 = l_Lean_mkAppB(x_99, x_80, x_79);
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
lean_dec_ref(x_80);
lean_dec_ref(x_79);
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
x_107 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
x_108 = l_Lean_Expr_isConstOf(x_106, x_107);
lean_dec_ref(x_106);
if (x_108 == 0)
{
lean_dec_ref(x_80);
lean_dec_ref(x_79);
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
x_109 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18;
lean_inc_ref(x_80);
x_110 = l_Lean_mkIntAdd(x_80, x_109);
lean_inc_ref(x_79);
x_111 = l_Lean_mkIntLE(x_110, x_79);
x_112 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24;
x_113 = l_Lean_mkAppB(x_112, x_80, x_79);
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
lean_dec_ref(x_80);
lean_dec_ref(x_79);
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
x_120 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
x_121 = l_Lean_Expr_isConstOf(x_119, x_120);
lean_dec_ref(x_119);
if (x_121 == 0)
{
lean_dec_ref(x_80);
lean_dec_ref(x_79);
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
lean_inc_ref(x_80);
lean_inc_ref(x_79);
x_122 = l_Lean_mkIntLE(x_79, x_80);
x_123 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27;
x_124 = l_Lean_mkAppB(x_123, x_80, x_79);
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
lean_dec_ref(x_80);
lean_dec_ref(x_79);
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
x_131 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
x_132 = l_Lean_Expr_isConstOf(x_130, x_131);
lean_dec_ref(x_130);
if (x_132 == 0)
{
lean_dec_ref(x_80);
lean_dec_ref(x_79);
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
lean_inc_ref(x_79);
lean_inc_ref(x_80);
x_133 = l_Lean_mkIntLE(x_80, x_79);
x_134 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30;
x_135 = l_Lean_mkAppB(x_134, x_80, x_79);
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
lean_dec_ref(x_80);
lean_dec_ref(x_79);
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
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_12);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5;
x_30 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6;
lean_inc(x_27);
x_31 = l_Lean_mkApp6(x_29, x_30, x_1, x_11, x_27, x_12, x_28);
lean_ctor_set(x_25, 1, x_31);
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5;
x_35 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6;
lean_inc(x_32);
x_36 = l_Lean_mkApp6(x_34, x_35, x_1, x_11, x_32, x_12, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_21, 0, x_37);
return x_19;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_21, 0);
lean_inc(x_38);
lean_dec(x_21);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5;
x_43 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6;
lean_inc(x_39);
x_44 = l_Lean_mkApp6(x_42, x_43, x_1, x_11, x_39, x_12, x_40);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_19, 0, x_46);
return x_19;
}
}
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_19, 0);
lean_inc(x_47);
lean_dec(x_19);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_11);
lean_ctor_set(x_48, 1, x_12);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_52 = x_47;
} else {
 lean_dec_ref(x_47);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_55 = x_51;
} else {
 lean_dec_ref(x_51);
 x_55 = lean_box(0);
}
x_56 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5;
x_57 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6;
lean_inc(x_53);
x_58 = l_Lean_mkApp6(x_56, x_57, x_1, x_11, x_53, x_12, x_54);
if (lean_is_scalar(x_55)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_55;
}
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_58);
if (lean_is_scalar(x_52)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_52;
}
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
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
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
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
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
x_2 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
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
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_33 = lean_box(0);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_81; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_40 = x_36;
} else {
 lean_dec_ref(x_36);
 x_40 = lean_box(0);
}
x_41 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6;
x_81 = lean_int_dec_eq(x_37, x_41);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_free_object(x_30);
x_82 = l_Lean_instInhabitedExpr;
lean_inc(x_39);
x_83 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_83, 0, x_82);
lean_closure_set(x_83, 1, x_39);
lean_inc(x_38);
lean_inc_ref(x_83);
x_84 = l_Int_Linear_Expr_denoteExpr___redArg(x_83, x_38);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_142; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_142 = lean_int_dec_le(x_41, x_37);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_143 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
x_144 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20;
x_145 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
x_146 = lean_int_neg(x_37);
x_147 = l_Int_toNat(x_146);
lean_dec(x_146);
x_148 = l_Lean_instToExprInt_mkNat(x_147);
x_149 = l_Lean_mkApp3(x_143, x_144, x_145, x_148);
x_87 = x_149;
goto block_141;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = l_Int_toNat(x_37);
x_151 = l_Lean_instToExprInt_mkNat(x_150);
x_87 = x_151;
goto block_141;
}
block_141:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_inc_ref(x_87);
x_88 = l_Lean_mkIntDvd(x_87, x_85);
x_89 = l_Int_Linear_Expr_norm(x_38);
lean_inc(x_37);
x_90 = l_Int_Linear_Poly_gcdCoeffs(x_89, x_37);
x_91 = l_Int_Linear_Poly_getConst(x_89);
x_92 = lean_int_emod(x_91, x_90);
lean_dec(x_91);
x_93 = lean_int_dec_eq(x_92, x_41);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_86);
lean_dec_ref(x_83);
lean_dec(x_37);
x_94 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_39, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9;
x_98 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8;
x_99 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_38);
x_100 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_101 = l_Lean_mkApp4(x_98, x_96, x_87, x_99, x_100);
x_102 = l_Lean_mkPropEq(x_88, x_97);
x_103 = l_Lean_Meta_mkExpectedPropHint(x_101, x_102);
if (lean_is_scalar(x_40)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_40;
}
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_103);
if (lean_is_scalar(x_35)) {
 x_105 = lean_alloc_ctor(1, 1, 0);
} else {
 x_105 = x_35;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_94, 0, x_105);
return x_94;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_106 = lean_ctor_get(x_94, 0);
lean_inc(x_106);
lean_dec(x_94);
x_107 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9;
x_108 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8;
x_109 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_38);
x_110 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_111 = l_Lean_mkApp4(x_108, x_106, x_87, x_109, x_110);
x_112 = l_Lean_mkPropEq(x_88, x_107);
x_113 = l_Lean_Meta_mkExpectedPropHint(x_111, x_112);
if (lean_is_scalar(x_40)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_40;
}
lean_ctor_set(x_114, 0, x_107);
lean_ctor_set(x_114, 1, x_113);
if (lean_is_scalar(x_35)) {
 x_115 = lean_alloc_ctor(1, 1, 0);
} else {
 x_115 = x_35;
}
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec_ref(x_88);
lean_dec_ref(x_87);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_35);
x_117 = !lean_is_exclusive(x_94);
if (x_117 == 0)
{
return x_94;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_94, 0);
lean_inc(x_118);
lean_dec(x_94);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_40);
lean_dec(x_35);
x_120 = l_Int_Linear_Poly_div(x_90, x_89);
lean_inc_ref(x_120);
x_121 = l_Int_Linear_Poly_toExpr(x_120);
x_122 = l_Int_Linear_instBEqExpr_beq(x_38, x_121);
lean_dec_ref(x_121);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_86);
lean_inc_ref(x_120);
x_123 = l_Int_Linear_Poly_denoteExpr___redArg(x_83, x_120);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = lean_int_ediv(x_37, x_90);
lean_dec(x_37);
x_126 = lean_int_dec_le(x_41, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_127 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
x_128 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20;
x_129 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
x_130 = lean_int_neg(x_125);
lean_dec(x_125);
x_131 = l_Int_toNat(x_130);
lean_dec(x_130);
x_132 = l_Lean_instToExprInt_mkNat(x_131);
x_133 = l_Lean_mkApp3(x_127, x_128, x_129, x_132);
x_42 = x_88;
x_43 = x_124;
x_44 = lean_box(0);
x_45 = x_90;
x_46 = x_87;
x_47 = x_120;
x_48 = x_133;
goto block_80;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = l_Int_toNat(x_125);
lean_dec(x_125);
x_135 = l_Lean_instToExprInt_mkNat(x_134);
x_42 = x_88;
x_43 = x_124;
x_44 = lean_box(0);
x_45 = x_90;
x_46 = x_87;
x_47 = x_120;
x_48 = x_135;
goto block_80;
}
}
else
{
uint8_t x_136; 
lean_dec_ref(x_120);
lean_dec(x_90);
lean_dec_ref(x_88);
lean_dec_ref(x_87);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_136 = !lean_is_exclusive(x_123);
if (x_136 == 0)
{
return x_123;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_123, 0);
lean_inc(x_137);
lean_dec(x_123);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; 
lean_dec_ref(x_120);
lean_dec(x_90);
lean_dec_ref(x_88);
lean_dec_ref(x_87);
lean_dec_ref(x_83);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_139 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_140 = lean_alloc_ctor(0, 1, 0);
} else {
 x_140 = x_86;
}
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
}
}
}
else
{
uint8_t x_152; 
lean_dec_ref(x_83);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_152 = !lean_is_exclusive(x_84);
if (x_152 == 0)
{
return x_84;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_84, 0);
lean_inc(x_153);
lean_dec(x_84);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
}
}
else
{
lean_object* x_155; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_155 = lean_box(0);
lean_ctor_set(x_30, 0, x_155);
return x_30;
}
block_80:
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_inc_ref(x_48);
x_49 = l_Lean_mkIntDvd(x_48, x_43);
x_50 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31;
x_51 = lean_int_dec_eq(x_45, x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_39, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2;
x_55 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_38);
x_56 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_47);
x_57 = lean_int_dec_le(x_41, x_45);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
x_59 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20;
x_60 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
x_61 = lean_int_neg(x_45);
lean_dec(x_45);
x_62 = l_Int_toNat(x_61);
lean_dec(x_61);
x_63 = l_Lean_instToExprInt_mkNat(x_62);
x_64 = l_Lean_mkApp3(x_58, x_59, x_60, x_63);
x_17 = x_42;
x_18 = x_56;
x_19 = x_54;
x_20 = x_55;
x_21 = lean_box(0);
x_22 = x_48;
x_23 = x_46;
x_24 = x_49;
x_25 = x_53;
x_26 = x_64;
goto block_29;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Int_toNat(x_45);
lean_dec(x_45);
x_66 = l_Lean_instToExprInt_mkNat(x_65);
x_17 = x_42;
x_18 = x_56;
x_19 = x_54;
x_20 = x_55;
x_21 = lean_box(0);
x_22 = x_48;
x_23 = x_46;
x_24 = x_49;
x_25 = x_53;
x_26 = x_66;
goto block_29;
}
}
else
{
uint8_t x_67; 
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_42);
lean_dec(x_38);
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
return x_52;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_52, 0);
lean_inc(x_68);
lean_dec(x_52);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; 
lean_dec_ref(x_48);
lean_dec(x_45);
x_70 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_39, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
x_72 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5;
x_73 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_38);
x_74 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_47);
x_75 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_76 = l_Lean_mkApp5(x_72, x_71, x_46, x_73, x_74, x_75);
x_7 = x_42;
x_8 = x_49;
x_9 = x_76;
x_10 = lean_box(0);
goto block_16;
}
else
{
uint8_t x_77; 
lean_dec_ref(x_49);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_42);
lean_dec(x_38);
x_77 = !lean_is_exclusive(x_70);
if (x_77 == 0)
{
return x_70;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_70, 0);
lean_inc(x_78);
lean_dec(x_70);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
}
}
}
else
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_30, 0);
lean_inc(x_156);
lean_dec(x_30);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_206; 
x_159 = lean_ctor_get(x_156, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_160 = x_156;
} else {
 lean_dec_ref(x_156);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 0);
lean_inc(x_162);
lean_dec(x_159);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_165 = x_161;
} else {
 lean_dec_ref(x_161);
 x_165 = lean_box(0);
}
x_166 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6;
x_206 = lean_int_dec_eq(x_162, x_166);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = l_Lean_instInhabitedExpr;
lean_inc(x_164);
x_208 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_208, 0, x_207);
lean_closure_set(x_208, 1, x_164);
lean_inc(x_163);
lean_inc_ref(x_208);
x_209 = l_Int_Linear_Expr_denoteExpr___redArg(x_208, x_163);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_257; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 x_211 = x_209;
} else {
 lean_dec_ref(x_209);
 x_211 = lean_box(0);
}
x_257 = lean_int_dec_le(x_166, x_162);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_258 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
x_259 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20;
x_260 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
x_261 = lean_int_neg(x_162);
x_262 = l_Int_toNat(x_261);
lean_dec(x_261);
x_263 = l_Lean_instToExprInt_mkNat(x_262);
x_264 = l_Lean_mkApp3(x_258, x_259, x_260, x_263);
x_212 = x_264;
goto block_256;
}
else
{
lean_object* x_265; lean_object* x_266; 
x_265 = l_Int_toNat(x_162);
x_266 = l_Lean_instToExprInt_mkNat(x_265);
x_212 = x_266;
goto block_256;
}
block_256:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
lean_inc_ref(x_212);
x_213 = l_Lean_mkIntDvd(x_212, x_210);
x_214 = l_Int_Linear_Expr_norm(x_163);
lean_inc(x_162);
x_215 = l_Int_Linear_Poly_gcdCoeffs(x_214, x_162);
x_216 = l_Int_Linear_Poly_getConst(x_214);
x_217 = lean_int_emod(x_216, x_215);
lean_dec(x_216);
x_218 = lean_int_dec_eq(x_217, x_166);
lean_dec(x_217);
if (x_218 == 0)
{
lean_object* x_219; 
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec(x_211);
lean_dec_ref(x_208);
lean_dec(x_162);
x_219 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_164, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 x_221 = x_219;
} else {
 lean_dec_ref(x_219);
 x_221 = lean_box(0);
}
x_222 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9;
x_223 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8;
x_224 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_163);
x_225 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_226 = l_Lean_mkApp4(x_223, x_220, x_212, x_224, x_225);
x_227 = l_Lean_mkPropEq(x_213, x_222);
x_228 = l_Lean_Meta_mkExpectedPropHint(x_226, x_227);
if (lean_is_scalar(x_165)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_165;
}
lean_ctor_set(x_229, 0, x_222);
lean_ctor_set(x_229, 1, x_228);
if (lean_is_scalar(x_160)) {
 x_230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_230 = x_160;
}
lean_ctor_set(x_230, 0, x_229);
if (lean_is_scalar(x_221)) {
 x_231 = lean_alloc_ctor(0, 1, 0);
} else {
 x_231 = x_221;
}
lean_ctor_set(x_231, 0, x_230);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec_ref(x_213);
lean_dec_ref(x_212);
lean_dec(x_165);
lean_dec(x_163);
lean_dec(x_160);
x_232 = lean_ctor_get(x_219, 0);
lean_inc(x_232);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 x_233 = x_219;
} else {
 lean_dec_ref(x_219);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 1, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_232);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; uint8_t x_237; 
lean_dec(x_165);
lean_dec(x_160);
x_235 = l_Int_Linear_Poly_div(x_215, x_214);
lean_inc_ref(x_235);
x_236 = l_Int_Linear_Poly_toExpr(x_235);
x_237 = l_Int_Linear_instBEqExpr_beq(x_163, x_236);
lean_dec_ref(x_236);
if (x_237 == 0)
{
lean_object* x_238; 
lean_dec(x_211);
lean_inc_ref(x_235);
x_238 = l_Int_Linear_Poly_denoteExpr___redArg(x_208, x_235);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
lean_dec_ref(x_238);
x_240 = lean_int_ediv(x_162, x_215);
lean_dec(x_162);
x_241 = lean_int_dec_le(x_166, x_240);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_242 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
x_243 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20;
x_244 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
x_245 = lean_int_neg(x_240);
lean_dec(x_240);
x_246 = l_Int_toNat(x_245);
lean_dec(x_245);
x_247 = l_Lean_instToExprInt_mkNat(x_246);
x_248 = l_Lean_mkApp3(x_242, x_243, x_244, x_247);
x_167 = x_213;
x_168 = x_239;
x_169 = lean_box(0);
x_170 = x_215;
x_171 = x_212;
x_172 = x_235;
x_173 = x_248;
goto block_205;
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = l_Int_toNat(x_240);
lean_dec(x_240);
x_250 = l_Lean_instToExprInt_mkNat(x_249);
x_167 = x_213;
x_168 = x_239;
x_169 = lean_box(0);
x_170 = x_215;
x_171 = x_212;
x_172 = x_235;
x_173 = x_250;
goto block_205;
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec_ref(x_235);
lean_dec(x_215);
lean_dec_ref(x_213);
lean_dec_ref(x_212);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_251 = lean_ctor_get(x_238, 0);
lean_inc(x_251);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 x_252 = x_238;
} else {
 lean_dec_ref(x_238);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 1, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_251);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; 
lean_dec_ref(x_235);
lean_dec(x_215);
lean_dec_ref(x_213);
lean_dec_ref(x_212);
lean_dec_ref(x_208);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_254 = lean_box(0);
if (lean_is_scalar(x_211)) {
 x_255 = lean_alloc_ctor(0, 1, 0);
} else {
 x_255 = x_211;
}
lean_ctor_set(x_255, 0, x_254);
return x_255;
}
}
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec_ref(x_208);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_160);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_267 = lean_ctor_get(x_209, 0);
lean_inc(x_267);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 x_268 = x_209;
} else {
 lean_dec_ref(x_209);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 1, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_267);
return x_269;
}
}
else
{
lean_object* x_270; lean_object* x_271; 
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_160);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_270 = lean_box(0);
x_271 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_271, 0, x_270);
return x_271;
}
block_205:
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; 
lean_inc_ref(x_173);
x_174 = l_Lean_mkIntDvd(x_173, x_168);
x_175 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31;
x_176 = lean_int_dec_eq(x_170, x_175);
if (x_176 == 0)
{
lean_object* x_177; 
x_177 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_164, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec_ref(x_177);
x_179 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2;
x_180 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_163);
x_181 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_172);
x_182 = lean_int_dec_le(x_166, x_170);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_183 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
x_184 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20;
x_185 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
x_186 = lean_int_neg(x_170);
lean_dec(x_170);
x_187 = l_Int_toNat(x_186);
lean_dec(x_186);
x_188 = l_Lean_instToExprInt_mkNat(x_187);
x_189 = l_Lean_mkApp3(x_183, x_184, x_185, x_188);
x_17 = x_167;
x_18 = x_181;
x_19 = x_179;
x_20 = x_180;
x_21 = lean_box(0);
x_22 = x_173;
x_23 = x_171;
x_24 = x_174;
x_25 = x_178;
x_26 = x_189;
goto block_29;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = l_Int_toNat(x_170);
lean_dec(x_170);
x_191 = l_Lean_instToExprInt_mkNat(x_190);
x_17 = x_167;
x_18 = x_181;
x_19 = x_179;
x_20 = x_180;
x_21 = lean_box(0);
x_22 = x_173;
x_23 = x_171;
x_24 = x_174;
x_25 = x_178;
x_26 = x_191;
goto block_29;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec_ref(x_174);
lean_dec_ref(x_173);
lean_dec_ref(x_172);
lean_dec_ref(x_171);
lean_dec(x_170);
lean_dec_ref(x_167);
lean_dec(x_163);
x_192 = lean_ctor_get(x_177, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 x_193 = x_177;
} else {
 lean_dec_ref(x_177);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_192);
return x_194;
}
}
else
{
lean_object* x_195; 
lean_dec_ref(x_173);
lean_dec(x_170);
x_195 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_164, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
lean_dec_ref(x_195);
x_197 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5;
x_198 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_163);
x_199 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_172);
x_200 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_201 = l_Lean_mkApp5(x_197, x_196, x_171, x_198, x_199, x_200);
x_7 = x_167;
x_8 = x_174;
x_9 = x_201;
x_10 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec_ref(x_174);
lean_dec_ref(x_172);
lean_dec_ref(x_171);
lean_dec_ref(x_167);
lean_dec(x_163);
x_202 = lean_ctor_get(x_195, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 x_203 = x_195;
} else {
 lean_dec_ref(x_195);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_202);
return x_204;
}
}
}
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
lean_inc_ref(x_8);
x_11 = l_Lean_mkPropEq(x_7, x_8);
x_12 = l_Lean_Meta_mkExpectedPropHint(x_9, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
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
x_27 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_28 = l_Lean_mkApp7(x_19, x_25, x_23, x_20, x_22, x_18, x_26, x_27);
x_7 = x_17;
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
lean_inc_ref(x_4);
return x_4;
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
x_3 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2;
x_4 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_18, 0, x_12);
lean_inc(x_11);
lean_inc_ref(x_18);
x_19 = l_Int_Linear_Expr_denoteExpr___redArg(x_18, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_inc_ref(x_13);
x_21 = l_Int_Linear_Poly_denoteExpr___redArg(x_18, x_13);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3;
x_25 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_11);
x_26 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_13);
x_27 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_28 = l_Lean_mkApp4(x_24, x_17, x_25, x_26, x_27);
lean_inc(x_23);
x_29 = l_Lean_mkIntEq(x_20, x_23);
x_30 = l_Lean_Meta_mkExpectedPropHint(x_28, x_29);
lean_ctor_set(x_9, 1, x_30);
lean_ctor_set(x_9, 0, x_23);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
lean_dec(x_21);
x_33 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3;
x_34 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_11);
x_35 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_13);
x_36 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_37 = l_Lean_mkApp4(x_33, x_17, x_34, x_35, x_36);
lean_inc(x_32);
x_38 = l_Lean_mkIntEq(x_20, x_32);
x_39 = l_Lean_Meta_mkExpectedPropHint(x_37, x_38);
lean_ctor_set(x_9, 1, x_39);
lean_ctor_set(x_9, 0, x_32);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_9);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_free_object(x_9);
lean_dec(x_11);
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
return x_21;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_21, 0);
lean_inc(x_43);
lean_dec(x_21);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_free_object(x_9);
lean_dec(x_11);
x_45 = !lean_is_exclusive(x_19);
if (x_45 == 0)
{
return x_19;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_19, 0);
lean_inc(x_46);
lean_dec(x_19);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec_ref(x_13);
lean_free_object(x_9);
lean_dec(x_12);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_16);
if (x_48 == 0)
{
return x_16;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_16, 0);
lean_inc(x_49);
lean_dec(x_16);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_dec_ref(x_13);
lean_free_object(x_9);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_51 = lean_box(0);
lean_ctor_set(x_7, 0, x_51);
return x_7;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_9, 0);
x_53 = lean_ctor_get(x_9, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_9);
x_54 = l_Int_Linear_Expr_norm(x_52);
lean_inc_ref(x_54);
x_55 = l_Int_Linear_Poly_toExpr(x_54);
x_56 = l_Int_Linear_instBEqExpr_beq(x_52, x_55);
lean_dec_ref(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_free_object(x_7);
lean_inc(x_53);
x_57 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_53, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_59, 0, x_53);
lean_inc(x_52);
lean_inc_ref(x_59);
x_60 = l_Int_Linear_Expr_denoteExpr___redArg(x_59, x_52);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
lean_inc_ref(x_54);
x_62 = l_Int_Linear_Poly_denoteExpr___redArg(x_59, x_54);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
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
x_66 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_52);
x_67 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_54);
x_68 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_69 = l_Lean_mkApp4(x_65, x_58, x_66, x_67, x_68);
lean_inc(x_63);
x_70 = l_Lean_mkIntEq(x_61, x_63);
x_71 = l_Lean_Meta_mkExpectedPropHint(x_69, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_63);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
if (lean_is_scalar(x_64)) {
 x_74 = lean_alloc_ctor(0, 1, 0);
} else {
 x_74 = x_64;
}
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_61);
lean_dec(x_58);
lean_dec_ref(x_54);
lean_dec(x_52);
x_75 = lean_ctor_get(x_62, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_76 = x_62;
} else {
 lean_dec_ref(x_62);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_54);
lean_dec(x_52);
x_78 = lean_ctor_get(x_60, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_79 = x_60;
} else {
 lean_dec_ref(x_60);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec(x_52);
x_81 = lean_ctor_get(x_57, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_82 = x_57;
} else {
 lean_dec_ref(x_57);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_81);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_84 = lean_box(0);
lean_ctor_set(x_7, 0, x_84);
return x_7;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_85 = lean_ctor_get(x_7, 0);
lean_inc(x_85);
lean_dec(x_7);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = l_Int_Linear_Expr_norm(x_86);
lean_inc_ref(x_89);
x_90 = l_Int_Linear_Poly_toExpr(x_89);
x_91 = l_Int_Linear_instBEqExpr_beq(x_86, x_90);
lean_dec_ref(x_90);
if (x_91 == 0)
{
lean_object* x_92; 
lean_inc(x_87);
x_92 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_87, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
x_94 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_94, 0, x_87);
lean_inc(x_86);
lean_inc_ref(x_94);
x_95 = l_Int_Linear_Expr_denoteExpr___redArg(x_94, x_86);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
lean_inc_ref(x_89);
x_97 = l_Int_Linear_Poly_denoteExpr___redArg(x_94, x_89);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
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
x_101 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_86);
x_102 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_89);
x_103 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_104 = l_Lean_mkApp4(x_100, x_93, x_101, x_102, x_103);
lean_inc(x_98);
x_105 = l_Lean_mkIntEq(x_96, x_98);
x_106 = l_Lean_Meta_mkExpectedPropHint(x_104, x_105);
if (lean_is_scalar(x_88)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_88;
}
lean_ctor_set(x_107, 0, x_98);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
if (lean_is_scalar(x_99)) {
 x_109 = lean_alloc_ctor(0, 1, 0);
} else {
 x_109 = x_99;
}
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_96);
lean_dec(x_93);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec(x_86);
x_110 = lean_ctor_get(x_97, 0);
lean_inc(x_110);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_111 = x_97;
} else {
 lean_dec_ref(x_97);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 1, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec(x_86);
x_113 = lean_ctor_get(x_95, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 x_114 = x_95;
} else {
 lean_dec_ref(x_95);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 1, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
x_116 = lean_ctor_get(x_92, 0);
lean_inc(x_116);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_117 = x_92;
} else {
 lean_dec_ref(x_92);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 1, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_116);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_121 = !lean_is_exclusive(x_7);
if (x_121 == 0)
{
return x_7;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_7, 0);
lean_inc(x_122);
lean_dec(x_7);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
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
l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45 = _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45);
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
l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30 = _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30);
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
