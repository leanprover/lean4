// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Int.Simp
// Imports: Lean.Meta.Tactic.Simp.Arith.Util Lean.Meta.Tactic.Simp.Arith.Int.Basic
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_denoteExpr___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__24;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__17;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1;
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__5;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__0;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntDvd(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__15;
lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___Lean_Meta_Simp_Arith_Int_simpEq_x3f_spec__0(lean_object*);
lean_object* l_Lean_mkIntEq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__19;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll___boxed(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__21;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__9;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__23;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19;
uint8_t l_Int_Linear_Poly_isValidLe(lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Expr_norm(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27___boxed(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6;
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14;
lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__1;
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_withAbstractAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll(lean_object*);
extern lean_object* l_Lean_levelOne;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__1;
uint8_t l_Int_Linear_Poly_isValidEq(lean_object*);
uint8_t l_Int_Linear_beqExpr____x40_Init_Data_Int_Linear_3091913453____hygCtx___hyg_120_(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10;
lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__22;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__12;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10;
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5;
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Expr_denoteExpr___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Nat_cast___at___Lean_Meta_Simp_Arith_Int_simpEq_x3f_spec__0(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_12 = l_Int_Linear_Expr_denoteExpr___redArg(x_11, x_2, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
lean_inc_ref(x_3);
lean_inc_ref(x_11);
x_16 = l_Int_Linear_Expr_denoteExpr___redArg(x_11, x_3, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_227; uint8_t x_337; 
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
x_20 = l_Lean_mkIntEq(x_13, x_17);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_96 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_96, 0, x_2);
lean_ctor_set(x_96, 1, x_3);
x_97 = l_Int_Linear_Expr_norm(x_96);
lean_dec_ref(x_96);
x_337 = l_Int_Linear_Poly_isUnsatEq(x_97);
if (x_337 == 0)
{
uint8_t x_338; 
x_338 = l_Int_Linear_Poly_isValidEq(x_97);
if (x_338 == 0)
{
lean_object* x_339; uint8_t x_340; 
lean_inc_ref(x_97);
x_339 = l_Int_Linear_Poly_toExpr(x_97);
x_340 = l_Int_Linear_beqExpr____x40_Init_Data_Int_Linear_3091913453____hygCtx___hyg_120_(x_339, x_2);
lean_dec_ref(x_339);
if (x_340 == 0)
{
x_227 = x_340;
goto block_336;
}
else
{
lean_object* x_341; uint8_t x_342; 
x_341 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__21;
x_342 = l_Int_Linear_beqExpr____x40_Init_Data_Int_Linear_3091913453____hygCtx___hyg_120_(x_3, x_341);
x_227 = x_342;
goto block_336;
}
}
else
{
lean_object* x_343; 
lean_dec_ref(x_97);
lean_dec(x_19);
lean_dec(x_15);
lean_dec_ref(x_11);
lean_dec_ref(x_1);
x_343 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_343) == 0)
{
uint8_t x_344; 
x_344 = !lean_is_exclusive(x_343);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_345 = lean_ctor_get(x_343, 0);
x_346 = lean_box(0);
x_347 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__24;
x_348 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_349 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__25;
x_350 = l_Lean_Name_mkStr3(x_4, x_348, x_349);
x_351 = l_Lean_mkConst(x_350, x_346);
x_352 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_353 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_354 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_355 = l_Lean_mkApp4(x_351, x_345, x_352, x_353, x_354);
x_356 = l_Lean_mkPropEq(x_20, x_347);
x_357 = l_Lean_Meta_mkExpectedPropHint(x_355, x_356);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_347);
lean_ctor_set(x_358, 1, x_357);
x_359 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_343, 0, x_359);
return x_343;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_360 = lean_ctor_get(x_343, 0);
x_361 = lean_ctor_get(x_343, 1);
lean_inc(x_361);
lean_inc(x_360);
lean_dec(x_343);
x_362 = lean_box(0);
x_363 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__24;
x_364 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_365 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__25;
x_366 = l_Lean_Name_mkStr3(x_4, x_364, x_365);
x_367 = l_Lean_mkConst(x_366, x_362);
x_368 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_369 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_370 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_371 = l_Lean_mkApp4(x_367, x_360, x_368, x_369, x_370);
x_372 = l_Lean_mkPropEq(x_20, x_363);
x_373 = l_Lean_Meta_mkExpectedPropHint(x_371, x_372);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_363);
lean_ctor_set(x_374, 1, x_373);
x_375 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_375, 0, x_374);
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_361);
return x_376;
}
}
else
{
uint8_t x_377; 
lean_dec_ref(x_20);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_377 = !lean_is_exclusive(x_343);
if (x_377 == 0)
{
return x_343;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_343, 0);
x_379 = lean_ctor_get(x_343, 1);
lean_inc(x_379);
lean_inc(x_378);
lean_dec(x_343);
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
return x_380;
}
}
}
}
else
{
lean_object* x_381; 
lean_dec_ref(x_97);
lean_dec(x_19);
lean_dec(x_15);
lean_dec_ref(x_11);
lean_dec_ref(x_1);
x_381 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_381) == 0)
{
uint8_t x_382; 
x_382 = !lean_is_exclusive(x_381);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_383 = lean_ctor_get(x_381, 0);
x_384 = lean_box(0);
x_385 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6;
x_386 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_387 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__26;
x_388 = l_Lean_Name_mkStr3(x_4, x_386, x_387);
x_389 = l_Lean_mkConst(x_388, x_384);
x_390 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_391 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_392 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_393 = l_Lean_mkApp4(x_389, x_383, x_390, x_391, x_392);
x_394 = l_Lean_mkPropEq(x_20, x_385);
x_395 = l_Lean_Meta_mkExpectedPropHint(x_393, x_394);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_385);
lean_ctor_set(x_396, 1, x_395);
x_397 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_381, 0, x_397);
return x_381;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_398 = lean_ctor_get(x_381, 0);
x_399 = lean_ctor_get(x_381, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_381);
x_400 = lean_box(0);
x_401 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6;
x_402 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_403 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__26;
x_404 = l_Lean_Name_mkStr3(x_4, x_402, x_403);
x_405 = l_Lean_mkConst(x_404, x_400);
x_406 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_407 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_408 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_409 = l_Lean_mkApp4(x_405, x_398, x_406, x_407, x_408);
x_410 = l_Lean_mkPropEq(x_20, x_401);
x_411 = l_Lean_Meta_mkExpectedPropHint(x_409, x_410);
x_412 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_412, 0, x_401);
lean_ctor_set(x_412, 1, x_411);
x_413 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_413, 0, x_412);
x_414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_399);
return x_414;
}
}
else
{
uint8_t x_415; 
lean_dec_ref(x_20);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_415 = !lean_is_exclusive(x_381);
if (x_415 == 0)
{
return x_381;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = lean_ctor_get(x_381, 0);
x_417 = lean_ctor_get(x_381, 1);
lean_inc(x_417);
lean_inc(x_416);
lean_dec(x_381);
x_418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
return x_418;
}
}
}
block_35:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_29 = l_Lean_mkApp5(x_25, x_23, x_22, x_26, x_27, x_28);
lean_inc_ref(x_21);
x_30 = l_Lean_mkPropEq(x_20, x_21);
x_31 = l_Lean_Meta_mkExpectedPropHint(x_29, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
if (lean_is_scalar(x_19)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_19;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
return x_34;
}
block_51:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_45 = l_Lean_mkApp6(x_41, x_36, x_39, x_42, x_38, x_43, x_44);
lean_inc_ref(x_37);
x_46 = l_Lean_mkPropEq(x_20, x_37);
x_47 = l_Lean_Meta_mkExpectedPropHint(x_45, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_37);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
if (lean_is_scalar(x_15)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_15;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_40);
return x_50;
}
block_95:
{
lean_object* x_55; 
x_55 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc_ref(x_54);
x_58 = l_Lean_mkIntEq(x_52, x_54);
x_59 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_60 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__2;
x_61 = l_Lean_Name_mkStr3(x_4, x_59, x_60);
x_62 = lean_box(0);
x_63 = l_Lean_mkConst(x_61, x_62);
x_64 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_65 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_66 = l_Lean_mkNatLit(x_53);
x_67 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_68 = l_Lean_mkApp6(x_63, x_57, x_64, x_65, x_66, x_54, x_67);
lean_inc_ref(x_58);
x_69 = l_Lean_mkPropEq(x_20, x_58);
x_70 = l_Lean_Meta_mkExpectedPropHint(x_68, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_58);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_55, 0, x_72);
return x_55;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_73 = lean_ctor_get(x_55, 0);
x_74 = lean_ctor_get(x_55, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_55);
lean_inc_ref(x_54);
x_75 = l_Lean_mkIntEq(x_52, x_54);
x_76 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_77 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__2;
x_78 = l_Lean_Name_mkStr3(x_4, x_76, x_77);
x_79 = lean_box(0);
x_80 = l_Lean_mkConst(x_78, x_79);
x_81 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_82 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_83 = l_Lean_mkNatLit(x_53);
x_84 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_85 = l_Lean_mkApp6(x_80, x_73, x_81, x_82, x_83, x_54, x_84);
lean_inc_ref(x_75);
x_86 = l_Lean_mkPropEq(x_20, x_75);
x_87 = l_Lean_Meta_mkExpectedPropHint(x_85, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_75);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_74);
return x_90;
}
}
else
{
uint8_t x_91; 
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_20);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_91 = !lean_is_exclusive(x_55);
if (x_91 == 0)
{
return x_55;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_55, 0);
x_93 = lean_ctor_get(x_55, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_55);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
block_226:
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = l_Int_Linear_Poly_gcdCoeffs_x27(x_97);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_dec_eq(x_103, x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_106 = l_Int_Linear_Poly_getConst(x_97);
x_107 = lean_nat_to_int(x_103);
x_108 = lean_int_emod(x_106, x_107);
lean_dec(x_106);
x_109 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
x_110 = lean_int_dec_eq(x_108, x_109);
lean_dec(x_108);
if (x_110 == 0)
{
lean_object* x_111; 
lean_dec_ref(x_97);
lean_dec(x_15);
lean_dec_ref(x_11);
x_111 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_98, x_99, x_100, x_101, x_102);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec_ref(x_111);
x_114 = lean_box(0);
x_115 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6;
x_116 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_117 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__7;
lean_inc_ref(x_4);
x_118 = l_Lean_Name_mkStr3(x_4, x_116, x_117);
x_119 = l_Lean_mkConst(x_118, x_114);
x_120 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_121 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_122 = lean_int_dec_le(x_109, x_107);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_123 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__13;
lean_inc_ref(x_4);
x_124 = l_Lean_Name_mkStr1(x_4);
x_125 = l_Lean_Expr_const___override(x_124, x_114);
x_126 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
x_127 = l_Lean_Name_mkStr2(x_4, x_126);
x_128 = l_Lean_Expr_const___override(x_127, x_114);
x_129 = lean_int_neg(x_107);
lean_dec(x_107);
x_130 = l_Int_toNat(x_129);
lean_dec(x_129);
x_131 = l_Lean_instToExprInt_mkNat(x_130);
x_132 = l_Lean_mkApp3(x_123, x_125, x_128, x_131);
x_21 = x_115;
x_22 = x_120;
x_23 = x_112;
x_24 = x_113;
x_25 = x_119;
x_26 = x_121;
x_27 = x_132;
goto block_35;
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec_ref(x_4);
x_133 = l_Int_toNat(x_107);
lean_dec(x_107);
x_134 = l_Lean_instToExprInt_mkNat(x_133);
x_21 = x_115;
x_22 = x_120;
x_23 = x_112;
x_24 = x_113;
x_25 = x_119;
x_26 = x_121;
x_27 = x_134;
goto block_35;
}
}
else
{
uint8_t x_135; 
lean_dec(x_107);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_135 = !lean_is_exclusive(x_111);
if (x_135 == 0)
{
return x_111;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_111, 0);
x_137 = lean_ctor_get(x_111, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_111);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_19);
x_139 = l_Int_Linear_Poly_div(x_107, x_97);
lean_inc_ref(x_139);
x_140 = l_Int_Linear_Poly_denoteExpr___redArg(x_11, x_139, x_102);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec_ref(x_140);
x_143 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_98, x_99, x_100, x_101, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec_ref(x_143);
x_146 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__15;
x_147 = l_Lean_mkIntEq(x_141, x_146);
x_148 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_149 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__16;
lean_inc_ref(x_4);
x_150 = l_Lean_Name_mkStr3(x_4, x_148, x_149);
x_151 = lean_box(0);
x_152 = l_Lean_mkConst(x_150, x_151);
x_153 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_154 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_155 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_139);
x_156 = lean_int_dec_le(x_109, x_107);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_157 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__13;
lean_inc_ref(x_4);
x_158 = l_Lean_Name_mkStr1(x_4);
x_159 = l_Lean_Expr_const___override(x_158, x_151);
x_160 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
x_161 = l_Lean_Name_mkStr2(x_4, x_160);
x_162 = l_Lean_Expr_const___override(x_161, x_151);
x_163 = lean_int_neg(x_107);
lean_dec(x_107);
x_164 = l_Int_toNat(x_163);
lean_dec(x_163);
x_165 = l_Lean_instToExprInt_mkNat(x_164);
x_166 = l_Lean_mkApp3(x_157, x_159, x_162, x_165);
x_36 = x_144;
x_37 = x_147;
x_38 = x_155;
x_39 = x_153;
x_40 = x_145;
x_41 = x_152;
x_42 = x_154;
x_43 = x_166;
goto block_51;
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec_ref(x_4);
x_167 = l_Int_toNat(x_107);
lean_dec(x_107);
x_168 = l_Lean_instToExprInt_mkNat(x_167);
x_36 = x_144;
x_37 = x_147;
x_38 = x_155;
x_39 = x_153;
x_40 = x_145;
x_41 = x_152;
x_42 = x_154;
x_43 = x_168;
goto block_51;
}
}
else
{
uint8_t x_169; 
lean_dec(x_141);
lean_dec_ref(x_139);
lean_dec(x_107);
lean_dec_ref(x_20);
lean_dec(x_15);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_169 = !lean_is_exclusive(x_143);
if (x_169 == 0)
{
return x_143;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_143, 0);
x_171 = lean_ctor_get(x_143, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_143);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
uint8_t x_173; 
lean_dec_ref(x_139);
lean_dec(x_107);
lean_dec(x_101);
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec_ref(x_20);
lean_dec(x_15);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_173 = !lean_is_exclusive(x_140);
if (x_173 == 0)
{
return x_140;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_140, 0);
x_175 = lean_ctor_get(x_140, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_140);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
}
else
{
lean_object* x_177; 
lean_dec(x_103);
lean_dec(x_19);
lean_dec(x_15);
lean_inc_ref(x_97);
x_177 = l_Int_Linear_Poly_denoteExpr___redArg(x_11, x_97, x_102);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec_ref(x_177);
x_180 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_98, x_99, x_100, x_101, x_179);
if (lean_obj_tag(x_180) == 0)
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_182 = lean_ctor_get(x_180, 0);
x_183 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__15;
x_184 = l_Lean_mkIntEq(x_178, x_183);
x_185 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_186 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__17;
x_187 = l_Lean_Name_mkStr3(x_4, x_185, x_186);
x_188 = lean_box(0);
x_189 = l_Lean_mkConst(x_187, x_188);
x_190 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_191 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_192 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_97);
x_193 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_194 = l_Lean_mkApp5(x_189, x_182, x_190, x_191, x_192, x_193);
lean_inc_ref(x_184);
x_195 = l_Lean_mkPropEq(x_20, x_184);
x_196 = l_Lean_Meta_mkExpectedPropHint(x_194, x_195);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_184);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_180, 0, x_198);
return x_180;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_199 = lean_ctor_get(x_180, 0);
x_200 = lean_ctor_get(x_180, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_180);
x_201 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__15;
x_202 = l_Lean_mkIntEq(x_178, x_201);
x_203 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_204 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__17;
x_205 = l_Lean_Name_mkStr3(x_4, x_203, x_204);
x_206 = lean_box(0);
x_207 = l_Lean_mkConst(x_205, x_206);
x_208 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_209 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_210 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_97);
x_211 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_212 = l_Lean_mkApp5(x_207, x_199, x_208, x_209, x_210, x_211);
lean_inc_ref(x_202);
x_213 = l_Lean_mkPropEq(x_20, x_202);
x_214 = l_Lean_Meta_mkExpectedPropHint(x_212, x_213);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_202);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_200);
return x_217;
}
}
else
{
uint8_t x_218; 
lean_dec(x_178);
lean_dec_ref(x_97);
lean_dec_ref(x_20);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_218 = !lean_is_exclusive(x_180);
if (x_218 == 0)
{
return x_180;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_180, 0);
x_220 = lean_ctor_get(x_180, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_180);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
uint8_t x_222; 
lean_dec(x_101);
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec_ref(x_97);
lean_dec_ref(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_222 = !lean_is_exclusive(x_177);
if (x_222 == 0)
{
return x_177;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_177, 0);
x_224 = lean_ctor_get(x_177, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_177);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
}
block_336:
{
if (x_227 == 0)
{
if (lean_obj_tag(x_97) == 0)
{
lean_dec_ref(x_1);
x_98 = x_6;
x_99 = x_7;
x_100 = x_8;
x_101 = x_9;
x_102 = x_18;
goto block_226;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_228 = lean_ctor_get(x_97, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_97, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_97, 2);
lean_inc_ref(x_230);
x_231 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__18;
x_232 = lean_int_dec_eq(x_228, x_231);
lean_dec(x_228);
if (x_232 == 0)
{
lean_dec_ref(x_230);
lean_dec(x_229);
lean_dec_ref(x_1);
x_98 = x_6;
x_99 = x_7;
x_100 = x_8;
x_101 = x_9;
x_102 = x_18;
goto block_226;
}
else
{
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
lean_dec_ref(x_97);
lean_dec(x_19);
lean_dec(x_15);
lean_dec_ref(x_11);
x_233 = lean_ctor_get(x_230, 0);
lean_inc(x_233);
lean_dec_ref(x_230);
x_234 = lean_array_get_borrowed(x_1, x_5, x_229);
x_235 = lean_int_neg(x_233);
lean_dec(x_233);
x_236 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
x_237 = lean_int_dec_le(x_236, x_235);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_238 = lean_box(0);
x_239 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__13;
lean_inc_ref(x_4);
x_240 = l_Lean_Name_mkStr1(x_4);
x_241 = l_Lean_Expr_const___override(x_240, x_238);
x_242 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
lean_inc_ref(x_4);
x_243 = l_Lean_Name_mkStr2(x_4, x_242);
x_244 = l_Lean_Expr_const___override(x_243, x_238);
x_245 = lean_int_neg(x_235);
lean_dec(x_235);
x_246 = l_Int_toNat(x_245);
lean_dec(x_245);
x_247 = l_Lean_instToExprInt_mkNat(x_246);
x_248 = l_Lean_mkApp3(x_239, x_241, x_244, x_247);
lean_inc_ref(x_234);
x_52 = x_234;
x_53 = x_229;
x_54 = x_248;
goto block_95;
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = l_Int_toNat(x_235);
lean_dec(x_235);
x_250 = l_Lean_instToExprInt_mkNat(x_249);
lean_inc_ref(x_234);
x_52 = x_234;
x_53 = x_229;
x_54 = x_250;
goto block_95;
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_251 = lean_ctor_get(x_230, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_230, 1);
lean_inc(x_252);
x_253 = lean_ctor_get(x_230, 2);
lean_inc_ref(x_253);
lean_dec_ref(x_230);
x_254 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__19;
x_255 = lean_int_dec_eq(x_251, x_254);
lean_dec(x_251);
if (x_255 == 0)
{
lean_dec_ref(x_253);
lean_dec(x_252);
lean_dec(x_229);
lean_dec_ref(x_1);
x_98 = x_6;
x_99 = x_7;
x_100 = x_8;
x_101 = x_9;
x_102 = x_18;
goto block_226;
}
else
{
if (lean_obj_tag(x_253) == 0)
{
uint8_t x_256; 
x_256 = !lean_is_exclusive(x_253);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_257 = lean_ctor_get(x_253, 0);
x_258 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
x_259 = lean_int_dec_eq(x_257, x_258);
lean_dec(x_257);
if (x_259 == 0)
{
lean_free_object(x_253);
lean_dec(x_252);
lean_dec(x_229);
lean_dec_ref(x_1);
x_98 = x_6;
x_99 = x_7;
x_100 = x_8;
x_101 = x_9;
x_102 = x_18;
goto block_226;
}
else
{
lean_object* x_260; 
lean_dec_ref(x_97);
lean_dec(x_19);
lean_dec(x_15);
lean_dec_ref(x_11);
lean_inc_ref(x_5);
x_260 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_260) == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_260);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_262 = lean_ctor_get(x_260, 0);
lean_inc_ref(x_1);
x_263 = lean_array_get(x_1, x_5, x_229);
x_264 = lean_array_get(x_1, x_5, x_252);
lean_dec_ref(x_5);
x_265 = l_Lean_mkIntEq(x_263, x_264);
x_266 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_267 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__20;
x_268 = l_Lean_Name_mkStr3(x_4, x_266, x_267);
x_269 = lean_box(0);
x_270 = l_Lean_mkConst(x_268, x_269);
x_271 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_272 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_273 = l_Lean_mkNatLit(x_229);
x_274 = l_Lean_mkNatLit(x_252);
x_275 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_276 = l_Lean_mkApp6(x_270, x_262, x_271, x_272, x_273, x_274, x_275);
lean_inc_ref(x_265);
x_277 = l_Lean_mkPropEq(x_20, x_265);
x_278 = l_Lean_Meta_mkExpectedPropHint(x_276, x_277);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_265);
lean_ctor_set(x_279, 1, x_278);
lean_ctor_set_tag(x_253, 1);
lean_ctor_set(x_253, 0, x_279);
lean_ctor_set(x_260, 0, x_253);
return x_260;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_280 = lean_ctor_get(x_260, 0);
x_281 = lean_ctor_get(x_260, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_260);
lean_inc_ref(x_1);
x_282 = lean_array_get(x_1, x_5, x_229);
x_283 = lean_array_get(x_1, x_5, x_252);
lean_dec_ref(x_5);
x_284 = l_Lean_mkIntEq(x_282, x_283);
x_285 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_286 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__20;
x_287 = l_Lean_Name_mkStr3(x_4, x_285, x_286);
x_288 = lean_box(0);
x_289 = l_Lean_mkConst(x_287, x_288);
x_290 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_291 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_292 = l_Lean_mkNatLit(x_229);
x_293 = l_Lean_mkNatLit(x_252);
x_294 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_295 = l_Lean_mkApp6(x_289, x_280, x_290, x_291, x_292, x_293, x_294);
lean_inc_ref(x_284);
x_296 = l_Lean_mkPropEq(x_20, x_284);
x_297 = l_Lean_Meta_mkExpectedPropHint(x_295, x_296);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_284);
lean_ctor_set(x_298, 1, x_297);
lean_ctor_set_tag(x_253, 1);
lean_ctor_set(x_253, 0, x_298);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_253);
lean_ctor_set(x_299, 1, x_281);
return x_299;
}
}
else
{
uint8_t x_300; 
lean_free_object(x_253);
lean_dec(x_252);
lean_dec(x_229);
lean_dec_ref(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_300 = !lean_is_exclusive(x_260);
if (x_300 == 0)
{
return x_260;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_260, 0);
x_302 = lean_ctor_get(x_260, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_260);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
}
}
else
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_304 = lean_ctor_get(x_253, 0);
lean_inc(x_304);
lean_dec(x_253);
x_305 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
x_306 = lean_int_dec_eq(x_304, x_305);
lean_dec(x_304);
if (x_306 == 0)
{
lean_dec(x_252);
lean_dec(x_229);
lean_dec_ref(x_1);
x_98 = x_6;
x_99 = x_7;
x_100 = x_8;
x_101 = x_9;
x_102 = x_18;
goto block_226;
}
else
{
lean_object* x_307; 
lean_dec_ref(x_97);
lean_dec(x_19);
lean_dec(x_15);
lean_dec_ref(x_11);
lean_inc_ref(x_5);
x_307 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_310 = x_307;
} else {
 lean_dec_ref(x_307);
 x_310 = lean_box(0);
}
lean_inc_ref(x_1);
x_311 = lean_array_get(x_1, x_5, x_229);
x_312 = lean_array_get(x_1, x_5, x_252);
lean_dec_ref(x_5);
x_313 = l_Lean_mkIntEq(x_311, x_312);
x_314 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_315 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__20;
x_316 = l_Lean_Name_mkStr3(x_4, x_314, x_315);
x_317 = lean_box(0);
x_318 = l_Lean_mkConst(x_316, x_317);
x_319 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_320 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_321 = l_Lean_mkNatLit(x_229);
x_322 = l_Lean_mkNatLit(x_252);
x_323 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_324 = l_Lean_mkApp6(x_318, x_308, x_319, x_320, x_321, x_322, x_323);
lean_inc_ref(x_313);
x_325 = l_Lean_mkPropEq(x_20, x_313);
x_326 = l_Lean_Meta_mkExpectedPropHint(x_324, x_325);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_313);
lean_ctor_set(x_327, 1, x_326);
x_328 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_328, 0, x_327);
if (lean_is_scalar(x_310)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_310;
}
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_309);
return x_329;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_252);
lean_dec(x_229);
lean_dec_ref(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_330 = lean_ctor_get(x_307, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_307, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_332 = x_307;
} else {
 lean_dec_ref(x_307);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(1, 2, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_330);
lean_ctor_set(x_333, 1, x_331);
return x_333;
}
}
}
}
else
{
lean_dec_ref(x_253);
lean_dec(x_252);
lean_dec(x_229);
lean_dec_ref(x_1);
x_98 = x_6;
x_99 = x_7;
x_100 = x_8;
x_101 = x_9;
x_102 = x_18;
goto block_226;
}
}
}
}
}
}
else
{
lean_object* x_334; lean_object* x_335; 
lean_dec_ref(x_97);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_15);
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
x_334 = lean_box(0);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_18);
return x_335;
}
}
}
else
{
uint8_t x_419; 
lean_dec(x_15);
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
x_419 = !lean_is_exclusive(x_16);
if (x_419 == 0)
{
return x_16;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_420 = lean_ctor_get(x_16, 0);
x_421 = lean_ctor_get(x_16, 1);
lean_inc(x_421);
lean_inc(x_420);
lean_dec(x_16);
x_422 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_422, 0, x_420);
lean_ctor_set(x_422, 1, x_421);
return x_422;
}
}
}
else
{
uint8_t x_423; 
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
x_423 = !lean_is_exclusive(x_12);
if (x_423 == 0)
{
return x_12;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_12, 0);
x_425 = lean_ctor_get(x_12, 1);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_12);
x_426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
return x_426;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_7 = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec_ref(x_8);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec_ref(x_7);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Lean_instInhabitedExpr;
x_22 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1), 10, 4);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_18);
lean_closure_set(x_23, 2, x_19);
lean_closure_set(x_23, 3, x_22);
x_24 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_25 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_20, x_24, x_23, x_2, x_3, x_4, x_5, x_17);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
return x_7;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_6);
lean_inc_ref(x_2);
lean_inc_ref(x_12);
x_13 = l_Int_Linear_Expr_denoteExpr___redArg(x_12, x_2, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_3);
lean_inc_ref(x_12);
x_17 = l_Int_Linear_Expr_denoteExpr___redArg(x_12, x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_192; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = l_Lean_mkIntLE(x_15, x_18);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_53 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_53, 0, x_2);
lean_ctor_set(x_53, 1, x_3);
x_54 = l_Int_Linear_Expr_norm(x_53);
lean_dec_ref(x_53);
x_192 = l_Int_Linear_Poly_isUnsatLe(x_54);
if (x_192 == 0)
{
uint8_t x_193; 
x_193 = l_Int_Linear_Poly_isValidLe(x_54);
if (x_193 == 0)
{
if (x_5 == 0)
{
lean_free_object(x_13);
goto block_191;
}
else
{
lean_object* x_194; uint8_t x_195; 
lean_inc_ref(x_54);
x_194 = l_Int_Linear_Poly_toExpr(x_54);
x_195 = l_Int_Linear_beqExpr____x40_Init_Data_Int_Linear_3091913453____hygCtx___hyg_120_(x_194, x_2);
lean_dec_ref(x_194);
if (x_195 == 0)
{
lean_free_object(x_13);
goto block_191;
}
else
{
lean_object* x_196; uint8_t x_197; 
x_196 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__21;
x_197 = l_Int_Linear_beqExpr____x40_Init_Data_Int_Linear_3091913453____hygCtx___hyg_120_(x_3, x_196);
if (x_197 == 0)
{
lean_free_object(x_13);
goto block_191;
}
else
{
lean_object* x_198; 
lean_dec_ref(x_54);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_198 = lean_box(0);
lean_ctor_set(x_13, 1, x_19);
lean_ctor_set(x_13, 0, x_198);
return x_13;
}
}
}
}
else
{
lean_object* x_199; 
lean_dec_ref(x_54);
lean_dec(x_20);
lean_free_object(x_13);
lean_dec_ref(x_12);
x_199 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_201 = lean_ctor_get(x_199, 0);
x_202 = lean_box(0);
x_203 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__24;
x_204 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_205 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__3;
x_206 = l_Lean_Name_mkStr3(x_4, x_204, x_205);
x_207 = l_Lean_mkConst(x_206, x_202);
x_208 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_209 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_210 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_211 = l_Lean_mkApp4(x_207, x_201, x_208, x_209, x_210);
x_212 = l_Lean_mkPropEq(x_21, x_203);
x_213 = l_Lean_Meta_mkExpectedPropHint(x_211, x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_203);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_199, 0, x_215);
return x_199;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_216 = lean_ctor_get(x_199, 0);
x_217 = lean_ctor_get(x_199, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_199);
x_218 = lean_box(0);
x_219 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__24;
x_220 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_221 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__3;
x_222 = l_Lean_Name_mkStr3(x_4, x_220, x_221);
x_223 = l_Lean_mkConst(x_222, x_218);
x_224 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_225 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_226 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_227 = l_Lean_mkApp4(x_223, x_216, x_224, x_225, x_226);
x_228 = l_Lean_mkPropEq(x_21, x_219);
x_229 = l_Lean_Meta_mkExpectedPropHint(x_227, x_228);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_219);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_231, 0, x_230);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_217);
return x_232;
}
}
else
{
uint8_t x_233; 
lean_dec_ref(x_21);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_233 = !lean_is_exclusive(x_199);
if (x_233 == 0)
{
return x_199;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_199, 0);
x_235 = lean_ctor_get(x_199, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_199);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
}
else
{
lean_object* x_237; 
lean_dec_ref(x_54);
lean_dec(x_20);
lean_free_object(x_13);
lean_dec_ref(x_12);
x_237 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_237) == 0)
{
uint8_t x_238; 
x_238 = !lean_is_exclusive(x_237);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_239 = lean_ctor_get(x_237, 0);
x_240 = lean_box(0);
x_241 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6;
x_242 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_243 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__4;
x_244 = l_Lean_Name_mkStr3(x_4, x_242, x_243);
x_245 = l_Lean_mkConst(x_244, x_240);
x_246 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_247 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_248 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_249 = l_Lean_mkApp4(x_245, x_239, x_246, x_247, x_248);
x_250 = l_Lean_mkPropEq(x_21, x_241);
x_251 = l_Lean_Meta_mkExpectedPropHint(x_249, x_250);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_241);
lean_ctor_set(x_252, 1, x_251);
x_253 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_237, 0, x_253);
return x_237;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_254 = lean_ctor_get(x_237, 0);
x_255 = lean_ctor_get(x_237, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_237);
x_256 = lean_box(0);
x_257 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6;
x_258 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_259 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__4;
x_260 = l_Lean_Name_mkStr3(x_4, x_258, x_259);
x_261 = l_Lean_mkConst(x_260, x_256);
x_262 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_263 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_264 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_265 = l_Lean_mkApp4(x_261, x_254, x_262, x_263, x_264);
x_266 = l_Lean_mkPropEq(x_21, x_257);
x_267 = l_Lean_Meta_mkExpectedPropHint(x_265, x_266);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_257);
lean_ctor_set(x_268, 1, x_267);
x_269 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_269, 0, x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_255);
return x_270;
}
}
else
{
uint8_t x_271; 
lean_dec_ref(x_21);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_271 = !lean_is_exclusive(x_237);
if (x_271 == 0)
{
return x_237;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_237, 0);
x_273 = lean_ctor_get(x_237, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_237);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
block_30:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc_ref(x_22);
x_25 = l_Lean_mkPropEq(x_21, x_22);
x_26 = l_Lean_Meta_mkExpectedPropHint(x_23, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
if (lean_is_scalar(x_20)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_20;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
block_41:
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_40 = l_Lean_mkApp6(x_31, x_36, x_33, x_32, x_34, x_38, x_39);
x_22 = x_37;
x_23 = x_40;
x_24 = x_35;
goto block_30;
}
block_52:
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_51 = l_Lean_mkApp6(x_47, x_44, x_42, x_48, x_45, x_49, x_50);
x_22 = x_46;
x_23 = x_51;
x_24 = x_43;
goto block_30;
}
block_131:
{
lean_object* x_59; lean_object* x_60; 
x_59 = l_Int_Linear_Poly_div(x_56, x_54);
lean_inc_ref(x_59);
x_60 = l_Int_Linear_Poly_denoteExpr___redArg(x_12, x_59, x_19);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = l_Lean_mkIntLit(x_57);
x_64 = l_Lean_mkIntLE(x_61, x_63);
if (x_58 == 0)
{
lean_object* x_65; 
x_65 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_62);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_68 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_69 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__0;
lean_inc_ref(x_4);
x_70 = l_Lean_Name_mkStr3(x_4, x_68, x_69);
x_71 = lean_box(0);
x_72 = l_Lean_mkConst(x_70, x_71);
x_73 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_74 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_75 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_59);
x_76 = lean_int_dec_le(x_57, x_56);
lean_dec(x_57);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_77 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10;
x_78 = l_Lean_Level_ofNat(x_55);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_71);
x_80 = l_Lean_Expr_const___override(x_77, x_79);
lean_inc_ref(x_4);
x_81 = l_Lean_Name_mkStr1(x_4);
x_82 = l_Lean_Expr_const___override(x_81, x_71);
x_83 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
x_84 = l_Lean_Name_mkStr2(x_4, x_83);
x_85 = l_Lean_Expr_const___override(x_84, x_71);
x_86 = lean_int_neg(x_56);
lean_dec(x_56);
x_87 = l_Int_toNat(x_86);
lean_dec(x_86);
x_88 = l_Lean_instToExprInt_mkNat(x_87);
x_89 = l_Lean_mkApp3(x_80, x_82, x_85, x_88);
x_31 = x_72;
x_32 = x_74;
x_33 = x_73;
x_34 = x_75;
x_35 = x_67;
x_36 = x_66;
x_37 = x_64;
x_38 = x_89;
goto block_41;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_4);
x_90 = l_Int_toNat(x_56);
lean_dec(x_56);
x_91 = l_Lean_instToExprInt_mkNat(x_90);
x_31 = x_72;
x_32 = x_74;
x_33 = x_73;
x_34 = x_75;
x_35 = x_67;
x_36 = x_66;
x_37 = x_64;
x_38 = x_91;
goto block_41;
}
}
else
{
uint8_t x_92; 
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_dec(x_57);
lean_dec(x_56);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_92 = !lean_is_exclusive(x_65);
if (x_92 == 0)
{
return x_65;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_65, 0);
x_94 = lean_ctor_get(x_65, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_65);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; 
x_96 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_62);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec_ref(x_96);
x_99 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_100 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__1;
lean_inc_ref(x_4);
x_101 = l_Lean_Name_mkStr3(x_4, x_99, x_100);
x_102 = lean_box(0);
x_103 = l_Lean_mkConst(x_101, x_102);
x_104 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_105 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_106 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_59);
x_107 = lean_int_dec_le(x_57, x_56);
lean_dec(x_57);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_108 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10;
x_109 = l_Lean_Level_ofNat(x_55);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_102);
x_111 = l_Lean_Expr_const___override(x_108, x_110);
lean_inc_ref(x_4);
x_112 = l_Lean_Name_mkStr1(x_4);
x_113 = l_Lean_Expr_const___override(x_112, x_102);
x_114 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
x_115 = l_Lean_Name_mkStr2(x_4, x_114);
x_116 = l_Lean_Expr_const___override(x_115, x_102);
x_117 = lean_int_neg(x_56);
lean_dec(x_56);
x_118 = l_Int_toNat(x_117);
lean_dec(x_117);
x_119 = l_Lean_instToExprInt_mkNat(x_118);
x_120 = l_Lean_mkApp3(x_111, x_113, x_116, x_119);
x_42 = x_104;
x_43 = x_98;
x_44 = x_97;
x_45 = x_106;
x_46 = x_64;
x_47 = x_103;
x_48 = x_105;
x_49 = x_120;
goto block_52;
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec_ref(x_4);
x_121 = l_Int_toNat(x_56);
lean_dec(x_56);
x_122 = l_Lean_instToExprInt_mkNat(x_121);
x_42 = x_104;
x_43 = x_98;
x_44 = x_97;
x_45 = x_106;
x_46 = x_64;
x_47 = x_103;
x_48 = x_105;
x_49 = x_122;
goto block_52;
}
}
else
{
uint8_t x_123; 
lean_dec_ref(x_64);
lean_dec_ref(x_59);
lean_dec(x_57);
lean_dec(x_56);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_123 = !lean_is_exclusive(x_96);
if (x_123 == 0)
{
return x_96;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_96, 0);
x_125 = lean_ctor_get(x_96, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_96);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
else
{
uint8_t x_127; 
lean_dec_ref(x_59);
lean_dec(x_57);
lean_dec(x_56);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_127 = !lean_is_exclusive(x_60);
if (x_127 == 0)
{
return x_60;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_60, 0);
x_129 = lean_ctor_get(x_60, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_60);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
block_191:
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = l_Int_Linear_Poly_gcdCoeffs_x27(x_54);
x_133 = lean_unsigned_to_nat(1u);
x_134 = lean_nat_dec_eq(x_132, x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_135 = l_Int_Linear_Poly_getConst(x_54);
x_136 = lean_nat_to_int(x_132);
x_137 = lean_int_emod(x_135, x_136);
lean_dec(x_135);
x_138 = lean_unsigned_to_nat(0u);
x_139 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
x_140 = lean_int_dec_eq(x_137, x_139);
lean_dec(x_137);
if (x_140 == 0)
{
uint8_t x_141; 
x_141 = 1;
x_55 = x_138;
x_56 = x_136;
x_57 = x_139;
x_58 = x_141;
goto block_131;
}
else
{
x_55 = x_138;
x_56 = x_136;
x_57 = x_139;
x_58 = x_134;
goto block_131;
}
}
else
{
lean_object* x_142; 
lean_dec(x_132);
lean_dec(x_20);
lean_inc_ref(x_54);
x_142 = l_Int_Linear_Poly_denoteExpr___redArg(x_12, x_54, x_19);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec_ref(x_142);
x_145 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_144);
if (lean_obj_tag(x_145) == 0)
{
uint8_t x_146; 
x_146 = !lean_is_exclusive(x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_147 = lean_ctor_get(x_145, 0);
x_148 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__15;
x_149 = l_Lean_mkIntLE(x_143, x_148);
x_150 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_151 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__2;
x_152 = l_Lean_Name_mkStr3(x_4, x_150, x_151);
x_153 = lean_box(0);
x_154 = l_Lean_mkConst(x_152, x_153);
x_155 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_156 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_157 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_54);
x_158 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_159 = l_Lean_mkApp5(x_154, x_147, x_155, x_156, x_157, x_158);
lean_inc_ref(x_149);
x_160 = l_Lean_mkPropEq(x_21, x_149);
x_161 = l_Lean_Meta_mkExpectedPropHint(x_159, x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_149);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_145, 0, x_163);
return x_145;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_164 = lean_ctor_get(x_145, 0);
x_165 = lean_ctor_get(x_145, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_145);
x_166 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__15;
x_167 = l_Lean_mkIntLE(x_143, x_166);
x_168 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_169 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__2;
x_170 = l_Lean_Name_mkStr3(x_4, x_168, x_169);
x_171 = lean_box(0);
x_172 = l_Lean_mkConst(x_170, x_171);
x_173 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_174 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_175 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_54);
x_176 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_177 = l_Lean_mkApp5(x_172, x_164, x_173, x_174, x_175, x_176);
lean_inc_ref(x_167);
x_178 = l_Lean_mkPropEq(x_21, x_167);
x_179 = l_Lean_Meta_mkExpectedPropHint(x_177, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_167);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_165);
return x_182;
}
}
else
{
uint8_t x_183; 
lean_dec(x_143);
lean_dec_ref(x_54);
lean_dec_ref(x_21);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_183 = !lean_is_exclusive(x_145);
if (x_183 == 0)
{
return x_145;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_145, 0);
x_185 = lean_ctor_get(x_145, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_145);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
else
{
uint8_t x_187; 
lean_dec_ref(x_54);
lean_dec_ref(x_21);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_187 = !lean_is_exclusive(x_142);
if (x_187 == 0)
{
return x_142;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_142, 0);
x_189 = lean_ctor_get(x_142, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_142);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
}
}
else
{
uint8_t x_275; 
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
x_275 = !lean_is_exclusive(x_17);
if (x_275 == 0)
{
return x_17;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_17, 0);
x_277 = lean_ctor_get(x_17, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_17);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_13, 0);
x_280 = lean_ctor_get(x_13, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_13);
lean_inc_ref(x_3);
lean_inc_ref(x_12);
x_281 = l_Int_Linear_Expr_denoteExpr___redArg(x_12, x_3, x_280);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; uint8_t x_439; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_284 = x_281;
} else {
 lean_dec_ref(x_281);
 x_284 = lean_box(0);
}
x_285 = l_Lean_mkIntLE(x_279, x_282);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_317 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_317, 0, x_2);
lean_ctor_set(x_317, 1, x_3);
x_318 = l_Int_Linear_Expr_norm(x_317);
lean_dec_ref(x_317);
x_439 = l_Int_Linear_Poly_isUnsatLe(x_318);
if (x_439 == 0)
{
uint8_t x_440; 
x_440 = l_Int_Linear_Poly_isValidLe(x_318);
if (x_440 == 0)
{
if (x_5 == 0)
{
goto block_438;
}
else
{
lean_object* x_441; uint8_t x_442; 
lean_inc_ref(x_318);
x_441 = l_Int_Linear_Poly_toExpr(x_318);
x_442 = l_Int_Linear_beqExpr____x40_Init_Data_Int_Linear_3091913453____hygCtx___hyg_120_(x_441, x_2);
lean_dec_ref(x_441);
if (x_442 == 0)
{
goto block_438;
}
else
{
lean_object* x_443; uint8_t x_444; 
x_443 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__21;
x_444 = l_Int_Linear_beqExpr____x40_Init_Data_Int_Linear_3091913453____hygCtx___hyg_120_(x_3, x_443);
if (x_444 == 0)
{
goto block_438;
}
else
{
lean_object* x_445; lean_object* x_446; 
lean_dec_ref(x_318);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_445 = lean_box(0);
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_283);
return x_446;
}
}
}
}
else
{
lean_object* x_447; 
lean_dec_ref(x_318);
lean_dec(x_284);
lean_dec_ref(x_12);
x_447 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_283);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_450 = x_447;
} else {
 lean_dec_ref(x_447);
 x_450 = lean_box(0);
}
x_451 = lean_box(0);
x_452 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__24;
x_453 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_454 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__3;
x_455 = l_Lean_Name_mkStr3(x_4, x_453, x_454);
x_456 = l_Lean_mkConst(x_455, x_451);
x_457 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_458 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_459 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_460 = l_Lean_mkApp4(x_456, x_448, x_457, x_458, x_459);
x_461 = l_Lean_mkPropEq(x_285, x_452);
x_462 = l_Lean_Meta_mkExpectedPropHint(x_460, x_461);
x_463 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_463, 0, x_452);
lean_ctor_set(x_463, 1, x_462);
x_464 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_464, 0, x_463);
if (lean_is_scalar(x_450)) {
 x_465 = lean_alloc_ctor(0, 2, 0);
} else {
 x_465 = x_450;
}
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_449);
return x_465;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_dec_ref(x_285);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_466 = lean_ctor_get(x_447, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_447, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_468 = x_447;
} else {
 lean_dec_ref(x_447);
 x_468 = lean_box(0);
}
if (lean_is_scalar(x_468)) {
 x_469 = lean_alloc_ctor(1, 2, 0);
} else {
 x_469 = x_468;
}
lean_ctor_set(x_469, 0, x_466);
lean_ctor_set(x_469, 1, x_467);
return x_469;
}
}
}
else
{
lean_object* x_470; 
lean_dec_ref(x_318);
lean_dec(x_284);
lean_dec_ref(x_12);
x_470 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_283);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_473 = x_470;
} else {
 lean_dec_ref(x_470);
 x_473 = lean_box(0);
}
x_474 = lean_box(0);
x_475 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6;
x_476 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_477 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__4;
x_478 = l_Lean_Name_mkStr3(x_4, x_476, x_477);
x_479 = l_Lean_mkConst(x_478, x_474);
x_480 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_481 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_482 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_483 = l_Lean_mkApp4(x_479, x_471, x_480, x_481, x_482);
x_484 = l_Lean_mkPropEq(x_285, x_475);
x_485 = l_Lean_Meta_mkExpectedPropHint(x_483, x_484);
x_486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_486, 0, x_475);
lean_ctor_set(x_486, 1, x_485);
x_487 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_487, 0, x_486);
if (lean_is_scalar(x_473)) {
 x_488 = lean_alloc_ctor(0, 2, 0);
} else {
 x_488 = x_473;
}
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_472);
return x_488;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec_ref(x_285);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_489 = lean_ctor_get(x_470, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_470, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_491 = x_470;
} else {
 lean_dec_ref(x_470);
 x_491 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_492 = lean_alloc_ctor(1, 2, 0);
} else {
 x_492 = x_491;
}
lean_ctor_set(x_492, 0, x_489);
lean_ctor_set(x_492, 1, x_490);
return x_492;
}
}
block_294:
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_inc_ref(x_286);
x_289 = l_Lean_mkPropEq(x_285, x_286);
x_290 = l_Lean_Meta_mkExpectedPropHint(x_287, x_289);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_286);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_292, 0, x_291);
if (lean_is_scalar(x_284)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_284;
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_288);
return x_293;
}
block_305:
{
lean_object* x_303; lean_object* x_304; 
x_303 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_304 = l_Lean_mkApp6(x_295, x_300, x_297, x_296, x_298, x_302, x_303);
x_286 = x_301;
x_287 = x_304;
x_288 = x_299;
goto block_294;
}
block_316:
{
lean_object* x_314; lean_object* x_315; 
x_314 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_315 = l_Lean_mkApp6(x_311, x_308, x_306, x_312, x_309, x_313, x_314);
x_286 = x_310;
x_287 = x_315;
x_288 = x_307;
goto block_294;
}
block_395:
{
lean_object* x_323; lean_object* x_324; 
x_323 = l_Int_Linear_Poly_div(x_320, x_318);
lean_inc_ref(x_323);
x_324 = l_Int_Linear_Poly_denoteExpr___redArg(x_12, x_323, x_283);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec_ref(x_324);
x_327 = l_Lean_mkIntLit(x_321);
x_328 = l_Lean_mkIntLE(x_325, x_327);
if (x_322 == 0)
{
lean_object* x_329; 
x_329 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_326);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec_ref(x_329);
x_332 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_333 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__0;
lean_inc_ref(x_4);
x_334 = l_Lean_Name_mkStr3(x_4, x_332, x_333);
x_335 = lean_box(0);
x_336 = l_Lean_mkConst(x_334, x_335);
x_337 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_338 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_339 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_323);
x_340 = lean_int_dec_le(x_321, x_320);
lean_dec(x_321);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_341 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10;
x_342 = l_Lean_Level_ofNat(x_319);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_335);
x_344 = l_Lean_Expr_const___override(x_341, x_343);
lean_inc_ref(x_4);
x_345 = l_Lean_Name_mkStr1(x_4);
x_346 = l_Lean_Expr_const___override(x_345, x_335);
x_347 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
x_348 = l_Lean_Name_mkStr2(x_4, x_347);
x_349 = l_Lean_Expr_const___override(x_348, x_335);
x_350 = lean_int_neg(x_320);
lean_dec(x_320);
x_351 = l_Int_toNat(x_350);
lean_dec(x_350);
x_352 = l_Lean_instToExprInt_mkNat(x_351);
x_353 = l_Lean_mkApp3(x_344, x_346, x_349, x_352);
x_295 = x_336;
x_296 = x_338;
x_297 = x_337;
x_298 = x_339;
x_299 = x_331;
x_300 = x_330;
x_301 = x_328;
x_302 = x_353;
goto block_305;
}
else
{
lean_object* x_354; lean_object* x_355; 
lean_dec_ref(x_4);
x_354 = l_Int_toNat(x_320);
lean_dec(x_320);
x_355 = l_Lean_instToExprInt_mkNat(x_354);
x_295 = x_336;
x_296 = x_338;
x_297 = x_337;
x_298 = x_339;
x_299 = x_331;
x_300 = x_330;
x_301 = x_328;
x_302 = x_355;
goto block_305;
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec_ref(x_328);
lean_dec_ref(x_323);
lean_dec(x_321);
lean_dec(x_320);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_356 = lean_ctor_get(x_329, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_329, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_358 = x_329;
} else {
 lean_dec_ref(x_329);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_356);
lean_ctor_set(x_359, 1, x_357);
return x_359;
}
}
else
{
lean_object* x_360; 
x_360 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_326);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec_ref(x_360);
x_363 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_364 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__1;
lean_inc_ref(x_4);
x_365 = l_Lean_Name_mkStr3(x_4, x_363, x_364);
x_366 = lean_box(0);
x_367 = l_Lean_mkConst(x_365, x_366);
x_368 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_369 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_370 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_323);
x_371 = lean_int_dec_le(x_321, x_320);
lean_dec(x_321);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_372 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10;
x_373 = l_Lean_Level_ofNat(x_319);
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_366);
x_375 = l_Lean_Expr_const___override(x_372, x_374);
lean_inc_ref(x_4);
x_376 = l_Lean_Name_mkStr1(x_4);
x_377 = l_Lean_Expr_const___override(x_376, x_366);
x_378 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
x_379 = l_Lean_Name_mkStr2(x_4, x_378);
x_380 = l_Lean_Expr_const___override(x_379, x_366);
x_381 = lean_int_neg(x_320);
lean_dec(x_320);
x_382 = l_Int_toNat(x_381);
lean_dec(x_381);
x_383 = l_Lean_instToExprInt_mkNat(x_382);
x_384 = l_Lean_mkApp3(x_375, x_377, x_380, x_383);
x_306 = x_368;
x_307 = x_362;
x_308 = x_361;
x_309 = x_370;
x_310 = x_328;
x_311 = x_367;
x_312 = x_369;
x_313 = x_384;
goto block_316;
}
else
{
lean_object* x_385; lean_object* x_386; 
lean_dec_ref(x_4);
x_385 = l_Int_toNat(x_320);
lean_dec(x_320);
x_386 = l_Lean_instToExprInt_mkNat(x_385);
x_306 = x_368;
x_307 = x_362;
x_308 = x_361;
x_309 = x_370;
x_310 = x_328;
x_311 = x_367;
x_312 = x_369;
x_313 = x_386;
goto block_316;
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec_ref(x_328);
lean_dec_ref(x_323);
lean_dec(x_321);
lean_dec(x_320);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_387 = lean_ctor_get(x_360, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_360, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_389 = x_360;
} else {
 lean_dec_ref(x_360);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(1, 2, 0);
} else {
 x_390 = x_389;
}
lean_ctor_set(x_390, 0, x_387);
lean_ctor_set(x_390, 1, x_388);
return x_390;
}
}
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_dec_ref(x_323);
lean_dec(x_321);
lean_dec(x_320);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_391 = lean_ctor_get(x_324, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_324, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_393 = x_324;
} else {
 lean_dec_ref(x_324);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(1, 2, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_392);
return x_394;
}
}
block_438:
{
lean_object* x_396; lean_object* x_397; uint8_t x_398; 
x_396 = l_Int_Linear_Poly_gcdCoeffs_x27(x_318);
x_397 = lean_unsigned_to_nat(1u);
x_398 = lean_nat_dec_eq(x_396, x_397);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; 
x_399 = l_Int_Linear_Poly_getConst(x_318);
x_400 = lean_nat_to_int(x_396);
x_401 = lean_int_emod(x_399, x_400);
lean_dec(x_399);
x_402 = lean_unsigned_to_nat(0u);
x_403 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
x_404 = lean_int_dec_eq(x_401, x_403);
lean_dec(x_401);
if (x_404 == 0)
{
uint8_t x_405; 
x_405 = 1;
x_319 = x_402;
x_320 = x_400;
x_321 = x_403;
x_322 = x_405;
goto block_395;
}
else
{
x_319 = x_402;
x_320 = x_400;
x_321 = x_403;
x_322 = x_398;
goto block_395;
}
}
else
{
lean_object* x_406; 
lean_dec(x_396);
lean_dec(x_284);
lean_inc_ref(x_318);
x_406 = l_Int_Linear_Poly_denoteExpr___redArg(x_12, x_318, x_283);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
lean_dec_ref(x_406);
x_409 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_408);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_412 = x_409;
} else {
 lean_dec_ref(x_409);
 x_412 = lean_box(0);
}
x_413 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__15;
x_414 = l_Lean_mkIntLE(x_407, x_413);
x_415 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_416 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___closed__2;
x_417 = l_Lean_Name_mkStr3(x_4, x_415, x_416);
x_418 = lean_box(0);
x_419 = l_Lean_mkConst(x_417, x_418);
x_420 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_421 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_422 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_318);
x_423 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_424 = l_Lean_mkApp5(x_419, x_410, x_420, x_421, x_422, x_423);
lean_inc_ref(x_414);
x_425 = l_Lean_mkPropEq(x_285, x_414);
x_426 = l_Lean_Meta_mkExpectedPropHint(x_424, x_425);
x_427 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_427, 0, x_414);
lean_ctor_set(x_427, 1, x_426);
x_428 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_428, 0, x_427);
if (lean_is_scalar(x_412)) {
 x_429 = lean_alloc_ctor(0, 2, 0);
} else {
 x_429 = x_412;
}
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_429, 1, x_411);
return x_429;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_407);
lean_dec_ref(x_318);
lean_dec_ref(x_285);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_430 = lean_ctor_get(x_409, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_409, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_432 = x_409;
} else {
 lean_dec_ref(x_409);
 x_432 = lean_box(0);
}
if (lean_is_scalar(x_432)) {
 x_433 = lean_alloc_ctor(1, 2, 0);
} else {
 x_433 = x_432;
}
lean_ctor_set(x_433, 0, x_430);
lean_ctor_set(x_433, 1, x_431);
return x_433;
}
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec_ref(x_318);
lean_dec_ref(x_285);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_434 = lean_ctor_get(x_406, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_406, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 x_436 = x_406;
} else {
 lean_dec_ref(x_406);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 2, 0);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_434);
lean_ctor_set(x_437, 1, x_435);
return x_437;
}
}
}
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_279);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_493 = lean_ctor_get(x_281, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_281, 1);
lean_inc(x_494);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_495 = x_281;
} else {
 lean_dec_ref(x_281);
 x_495 = lean_box(0);
}
if (lean_is_scalar(x_495)) {
 x_496 = lean_alloc_ctor(1, 2, 0);
} else {
 x_496 = x_495;
}
lean_ctor_set(x_496, 0, x_493);
lean_ctor_set(x_496, 1, x_494);
return x_496;
}
}
}
else
{
uint8_t x_497; 
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_497 = !lean_is_exclusive(x_13);
if (x_497 == 0)
{
return x_13;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = lean_ctor_get(x_13, 0);
x_499 = lean_ctor_get(x_13, 1);
lean_inc(x_499);
lean_inc(x_498);
lean_dec(x_13);
x_500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_499);
return x_500;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_34; uint8_t x_35; 
x_8 = l_Lean_instInhabitedExpr;
x_34 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2;
x_35 = l_Lean_Expr_isAppOf(x_1, x_34);
if (x_35 == 0)
{
x_9 = x_35;
goto block_33;
}
else
{
x_9 = x_2;
goto block_33;
}
block_33:
{
lean_object* x_10; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_10 = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec_ref(x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec_ref(x_10);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_25 = lean_box(x_9);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___boxed), 11, 5);
lean_closure_set(x_26, 0, x_8);
lean_closure_set(x_26, 1, x_21);
lean_closure_set(x_26, 2, x_22);
lean_closure_set(x_26, 3, x_24);
lean_closure_set(x_26, 4, x_25);
x_27 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_28 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_23, x_27, x_26, x_3, x_4, x_5, x_6, x_20);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
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
x_13 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
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
x_15 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_13, x_14, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec_ref(x_1);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_2, 0, x_19);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_2, 0, x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_2);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_15, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
x_30 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__5;
x_31 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__6;
lean_inc(x_28);
x_32 = l_Lean_mkApp6(x_30, x_31, x_1, x_13, x_28, x_3, x_29);
lean_ctor_set(x_25, 1, x_32);
return x_15;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__5;
x_36 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__6;
lean_inc(x_33);
x_37 = l_Lean_mkApp6(x_35, x_36, x_1, x_13, x_33, x_3, x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_16, 0, x_38);
return x_15;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_43 = x_39;
} else {
 lean_dec_ref(x_39);
 x_43 = lean_box(0);
}
x_44 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__5;
x_45 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__6;
lean_inc(x_41);
x_46 = l_Lean_mkApp6(x_44, x_45, x_1, x_13, x_41, x_3, x_42);
if (lean_is_scalar(x_43)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_43;
}
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_16, 0, x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_16);
lean_ctor_set(x_48, 1, x_40);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_16, 0);
lean_inc(x_49);
lean_dec(x_16);
x_50 = lean_ctor_get(x_15, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_51 = x_15;
} else {
 lean_dec_ref(x_15);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_54 = x_49;
} else {
 lean_dec_ref(x_49);
 x_54 = lean_box(0);
}
x_55 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__5;
x_56 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__6;
lean_inc(x_52);
x_57 = l_Lean_mkApp6(x_55, x_56, x_1, x_13, x_52, x_3, x_53);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
return x_60;
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
lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_2, 0);
lean_inc(x_61);
lean_dec(x_2);
x_62 = 0;
lean_inc(x_61);
x_63 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_61, x_62, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_1);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_3);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_66;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_63, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_73 = x_63;
} else {
 lean_dec_ref(x_63);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_76 = x_70;
} else {
 lean_dec_ref(x_70);
 x_76 = lean_box(0);
}
x_77 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__5;
x_78 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___closed__6;
lean_inc(x_74);
x_79 = l_Lean_mkApp6(x_77, x_78, x_1, x_61, x_74, x_3, x_75);
if (lean_is_scalar(x_76)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_76;
}
lean_ctor_set(x_80, 0, x_74);
lean_ctor_set(x_80, 1, x_79);
if (lean_is_scalar(x_71)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_71;
}
lean_ctor_set(x_81, 0, x_80);
if (lean_is_scalar(x_73)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_73;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_72);
return x_82;
}
}
else
{
lean_dec(x_61);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_63;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_1, x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_appArg_x21(x_1);
x_13 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_12, x_3, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_25; uint8_t x_26; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_box(0);
x_17 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4;
x_25 = l_Lean_Expr_cleanupAnnotations(x_14);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
goto block_24;
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_inc_ref(x_25);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_25);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
goto block_24;
}
else
{
lean_object* x_29; uint8_t x_30; 
lean_inc_ref(x_27);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_30 = l_Lean_Expr_isApp(x_29);
if (x_30 == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_27);
lean_dec_ref(x_25);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
goto block_24;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_29);
x_32 = l_Lean_Expr_isApp(x_31);
if (x_32 == 0)
{
lean_dec_ref(x_31);
lean_dec_ref(x_27);
lean_dec_ref(x_25);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
goto block_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_33);
lean_dec_ref(x_25);
x_34 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_34);
lean_dec_ref(x_27);
x_35 = lean_ctor_get(x_31, 1);
lean_inc_ref(x_35);
x_36 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_37 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7;
x_38 = l_Lean_Expr_isConstOf(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10;
x_40 = l_Lean_Expr_isConstOf(x_36, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13;
x_42 = l_Lean_Expr_isConstOf(x_36, x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2;
x_44 = l_Lean_Expr_isConstOf(x_36, x_43);
lean_dec_ref(x_36);
if (x_44 == 0)
{
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
goto block_24;
}
else
{
lean_object* x_45; 
x_45 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_35, x_3, x_15);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = l_Lean_Expr_cleanupAnnotations(x_46);
x_49 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_50 = l_Lean_Expr_isConstOf(x_48, x_49);
lean_dec_ref(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_34);
lean_dec_ref(x_33);
x_51 = lean_box(0);
x_52 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_16, x_17, x_51, x_2, x_3, x_4, x_5, x_47);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14;
lean_inc_ref(x_33);
x_54 = l_Lean_mkIntAdd(x_33, x_53);
lean_inc_ref(x_34);
x_55 = l_Lean_mkIntLE(x_54, x_34);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17;
x_58 = l_Lean_mkAppB(x_57, x_34, x_33);
x_59 = lean_box(0);
x_60 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_56, x_58, x_59, x_2, x_3, x_4, x_5, x_47);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_61 = !lean_is_exclusive(x_45);
if (x_61 == 0)
{
return x_45;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_45, 0);
x_63 = lean_ctor_get(x_45, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_45);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
lean_object* x_65; 
lean_dec_ref(x_36);
x_65 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_35, x_3, x_15);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_68 = l_Lean_Expr_cleanupAnnotations(x_66);
x_69 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_70 = l_Lean_Expr_isConstOf(x_68, x_69);
lean_dec_ref(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_34);
lean_dec_ref(x_33);
x_71 = lean_box(0);
x_72 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_16, x_17, x_71, x_2, x_3, x_4, x_5, x_67);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_73 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14;
lean_inc_ref(x_34);
x_74 = l_Lean_mkIntAdd(x_34, x_73);
lean_inc_ref(x_33);
x_75 = l_Lean_mkIntLE(x_74, x_33);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20;
x_78 = l_Lean_mkAppB(x_77, x_34, x_33);
x_79 = lean_box(0);
x_80 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_76, x_78, x_79, x_2, x_3, x_4, x_5, x_67);
return x_80;
}
}
else
{
uint8_t x_81; 
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_81 = !lean_is_exclusive(x_65);
if (x_81 == 0)
{
return x_65;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_65, 0);
x_83 = lean_ctor_get(x_65, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_65);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
else
{
lean_object* x_85; 
lean_dec_ref(x_36);
x_85 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_35, x_3, x_15);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec_ref(x_85);
x_88 = l_Lean_Expr_cleanupAnnotations(x_86);
x_89 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_90 = l_Lean_Expr_isConstOf(x_88, x_89);
lean_dec_ref(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_34);
lean_dec_ref(x_33);
x_91 = lean_box(0);
x_92 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_16, x_17, x_91, x_2, x_3, x_4, x_5, x_87);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_inc_ref(x_34);
lean_inc_ref(x_33);
x_93 = l_Lean_mkIntLE(x_33, x_34);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23;
x_96 = l_Lean_mkAppB(x_95, x_34, x_33);
x_97 = lean_box(0);
x_98 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_94, x_96, x_97, x_2, x_3, x_4, x_5, x_87);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_99 = !lean_is_exclusive(x_85);
if (x_99 == 0)
{
return x_85;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_85, 0);
x_101 = lean_ctor_get(x_85, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_85);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
else
{
lean_object* x_103; 
lean_dec_ref(x_36);
x_103 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_35, x_3, x_15);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec_ref(x_103);
x_106 = l_Lean_Expr_cleanupAnnotations(x_104);
x_107 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_108 = l_Lean_Expr_isConstOf(x_106, x_107);
lean_dec_ref(x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec_ref(x_34);
lean_dec_ref(x_33);
x_109 = lean_box(0);
x_110 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_16, x_17, x_109, x_2, x_3, x_4, x_5, x_105);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_inc_ref(x_33);
lean_inc_ref(x_34);
x_111 = l_Lean_mkIntLE(x_34, x_33);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26;
x_114 = l_Lean_mkAppB(x_113, x_34, x_33);
x_115 = lean_box(0);
x_116 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_112, x_114, x_115, x_2, x_3, x_4, x_5, x_105);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_117 = !lean_is_exclusive(x_103);
if (x_117 == 0)
{
return x_103;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_103, 0);
x_119 = lean_ctor_get(x_103, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_103);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
}
}
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_16, x_17, x_22, x_18, x_19, x_20, x_21, x_15);
return x_23;
}
}
else
{
uint8_t x_121; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_121 = !lean_is_exclusive(x_13);
if (x_121 == 0)
{
return x_13;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_13, 0);
x_123 = lean_ctor_get(x_13, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_13);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_93; lean_object* x_94; 
lean_inc_ref(x_7);
x_93 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_93, 0, x_1);
lean_closure_set(x_93, 1, x_7);
lean_inc_ref(x_2);
lean_inc_ref(x_93);
x_94 = l_Int_Linear_Expr_denoteExpr___redArg(x_93, x_2, x_12);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_172; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
x_172 = lean_int_dec_le(x_4, x_6);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_173 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10;
x_174 = l_Lean_Level_ofNat(x_5);
x_175 = lean_box(0);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lean_Expr_const___override(x_173, x_176);
lean_inc_ref(x_3);
x_178 = l_Lean_Name_mkStr1(x_3);
x_179 = l_Lean_Expr_const___override(x_178, x_175);
x_180 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
lean_inc_ref(x_3);
x_181 = l_Lean_Name_mkStr2(x_3, x_180);
x_182 = l_Lean_Expr_const___override(x_181, x_175);
x_183 = lean_int_neg(x_6);
x_184 = l_Int_toNat(x_183);
lean_dec(x_183);
x_185 = l_Lean_instToExprInt_mkNat(x_184);
x_186 = l_Lean_mkApp3(x_177, x_179, x_182, x_185);
x_98 = x_186;
goto block_171;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = l_Int_toNat(x_6);
x_188 = l_Lean_instToExprInt_mkNat(x_187);
x_98 = x_188;
goto block_171;
}
block_171:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_inc_ref(x_98);
x_99 = l_Lean_mkIntDvd(x_98, x_95);
x_100 = l_Int_Linear_Expr_norm(x_2);
lean_inc(x_6);
x_101 = l_Int_Linear_Poly_gcdCoeffs(x_100, x_6);
x_102 = l_Int_Linear_Poly_getConst(x_100);
x_103 = lean_int_emod(x_102, x_101);
lean_dec(x_102);
x_104 = lean_int_dec_eq(x_103, x_4);
lean_dec(x_103);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_101);
lean_dec_ref(x_100);
lean_dec(x_97);
lean_dec_ref(x_93);
lean_dec(x_6);
x_105 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_7, x_8, x_9, x_10, x_11, x_96);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = lean_box(0);
x_109 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6;
x_110 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_111 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__2;
x_112 = l_Lean_Name_mkStr3(x_3, x_110, x_111);
x_113 = l_Lean_mkConst(x_112, x_108);
x_114 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_115 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_116 = l_Lean_mkApp4(x_113, x_107, x_98, x_114, x_115);
x_117 = l_Lean_mkPropEq(x_99, x_109);
x_118 = l_Lean_Meta_mkExpectedPropHint(x_116, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_109);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_105, 0, x_120);
return x_105;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_121 = lean_ctor_get(x_105, 0);
x_122 = lean_ctor_get(x_105, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_105);
x_123 = lean_box(0);
x_124 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__6;
x_125 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_126 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__2;
x_127 = l_Lean_Name_mkStr3(x_3, x_125, x_126);
x_128 = l_Lean_mkConst(x_127, x_123);
x_129 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_130 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_131 = l_Lean_mkApp4(x_128, x_121, x_98, x_129, x_130);
x_132 = l_Lean_mkPropEq(x_99, x_124);
x_133 = l_Lean_Meta_mkExpectedPropHint(x_131, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_124);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_122);
return x_136;
}
}
else
{
uint8_t x_137; 
lean_dec_ref(x_99);
lean_dec_ref(x_98);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_137 = !lean_is_exclusive(x_105);
if (x_137 == 0)
{
return x_105;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_105, 0);
x_139 = lean_ctor_get(x_105, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_105);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = l_Int_Linear_Poly_div(x_101, x_100);
lean_inc_ref(x_141);
x_142 = l_Int_Linear_Poly_toExpr(x_141);
x_143 = l_Int_Linear_beqExpr____x40_Init_Data_Int_Linear_3091913453____hygCtx___hyg_120_(x_2, x_142);
lean_dec_ref(x_142);
if (x_143 == 0)
{
lean_object* x_144; 
lean_dec(x_97);
lean_inc_ref(x_141);
x_144 = l_Int_Linear_Poly_denoteExpr___redArg(x_93, x_141, x_96);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec_ref(x_144);
x_147 = lean_int_ediv(x_6, x_101);
lean_dec(x_6);
x_148 = lean_int_dec_le(x_4, x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_149 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10;
x_150 = l_Lean_Level_ofNat(x_5);
x_151 = lean_box(0);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = l_Lean_Expr_const___override(x_149, x_152);
lean_inc_ref(x_3);
x_154 = l_Lean_Name_mkStr1(x_3);
x_155 = l_Lean_Expr_const___override(x_154, x_151);
x_156 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
lean_inc_ref(x_3);
x_157 = l_Lean_Name_mkStr2(x_3, x_156);
x_158 = l_Lean_Expr_const___override(x_157, x_151);
x_159 = lean_int_neg(x_147);
lean_dec(x_147);
x_160 = l_Int_toNat(x_159);
lean_dec(x_159);
x_161 = l_Lean_instToExprInt_mkNat(x_160);
x_162 = l_Lean_mkApp3(x_153, x_155, x_158, x_161);
x_36 = x_99;
x_37 = x_141;
x_38 = x_101;
x_39 = x_146;
x_40 = x_98;
x_41 = x_145;
x_42 = x_162;
goto block_92;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Int_toNat(x_147);
lean_dec(x_147);
x_164 = l_Lean_instToExprInt_mkNat(x_163);
x_36 = x_99;
x_37 = x_141;
x_38 = x_101;
x_39 = x_146;
x_40 = x_98;
x_41 = x_145;
x_42 = x_164;
goto block_92;
}
}
else
{
uint8_t x_165; 
lean_dec_ref(x_141);
lean_dec(x_101);
lean_dec_ref(x_99);
lean_dec_ref(x_98);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_165 = !lean_is_exclusive(x_144);
if (x_165 == 0)
{
return x_144;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_144, 0);
x_167 = lean_ctor_get(x_144, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_144);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec_ref(x_141);
lean_dec(x_101);
lean_dec_ref(x_99);
lean_dec_ref(x_98);
lean_dec_ref(x_93);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_169 = lean_box(0);
if (lean_is_scalar(x_97)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_97;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_96);
return x_170;
}
}
}
}
else
{
uint8_t x_189; 
lean_dec_ref(x_93);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_189 = !lean_is_exclusive(x_94);
if (x_189 == 0)
{
return x_94;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_94, 0);
x_191 = lean_ctor_get(x_94, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_94);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_34 = l_Lean_mkApp7(x_27, x_30, x_31, x_29, x_24, x_25, x_32, x_33);
x_13 = x_23;
x_14 = x_26;
x_15 = x_34;
x_16 = x_28;
goto block_22;
}
block_92:
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_inc_ref(x_42);
x_43 = l_Lean_mkIntDvd(x_42, x_41);
x_44 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__18;
x_45 = lean_int_dec_eq(x_38, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_7, x_8, x_9, x_10, x_11, x_39);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_50 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__0;
lean_inc_ref(x_3);
x_51 = l_Lean_Name_mkStr3(x_3, x_49, x_50);
x_52 = lean_box(0);
x_53 = l_Lean_mkConst(x_51, x_52);
x_54 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_55 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_37);
x_56 = lean_int_dec_le(x_4, x_38);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_57 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__10;
x_58 = l_Lean_Level_ofNat(x_5);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_52);
x_60 = l_Lean_Expr_const___override(x_57, x_59);
lean_inc_ref(x_3);
x_61 = l_Lean_Name_mkStr1(x_3);
x_62 = l_Lean_Expr_const___override(x_61, x_52);
x_63 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__14;
x_64 = l_Lean_Name_mkStr2(x_3, x_63);
x_65 = l_Lean_Expr_const___override(x_64, x_52);
x_66 = lean_int_neg(x_38);
lean_dec(x_38);
x_67 = l_Int_toNat(x_66);
lean_dec(x_66);
x_68 = l_Lean_instToExprInt_mkNat(x_67);
x_69 = l_Lean_mkApp3(x_60, x_62, x_65, x_68);
x_23 = x_36;
x_24 = x_42;
x_25 = x_55;
x_26 = x_43;
x_27 = x_53;
x_28 = x_48;
x_29 = x_54;
x_30 = x_47;
x_31 = x_40;
x_32 = x_69;
goto block_35;
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec_ref(x_3);
x_70 = l_Int_toNat(x_38);
lean_dec(x_38);
x_71 = l_Lean_instToExprInt_mkNat(x_70);
x_23 = x_36;
x_24 = x_42;
x_25 = x_55;
x_26 = x_43;
x_27 = x_53;
x_28 = x_48;
x_29 = x_54;
x_30 = x_47;
x_31 = x_40;
x_32 = x_71;
goto block_35;
}
}
else
{
uint8_t x_72; 
lean_dec_ref(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_40);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_72 = !lean_is_exclusive(x_46);
if (x_72 == 0)
{
return x_46;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_46, 0);
x_74 = lean_ctor_get(x_46, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_46);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; 
lean_dec_ref(x_42);
lean_dec(x_38);
x_76 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_7, x_8, x_9, x_10, x_11, x_39);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
x_79 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_80 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___closed__1;
x_81 = l_Lean_Name_mkStr3(x_3, x_79, x_80);
x_82 = lean_box(0);
x_83 = l_Lean_mkConst(x_81, x_82);
x_84 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_85 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_37);
x_86 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_87 = l_Lean_mkApp5(x_83, x_77, x_40, x_84, x_85, x_86);
x_13 = x_36;
x_14 = x_43;
x_15 = x_87;
x_16 = x_78;
goto block_22;
}
else
{
uint8_t x_88; 
lean_dec_ref(x_43);
lean_dec_ref(x_40);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_88 = !lean_is_exclusive(x_76);
if (x_88 == 0)
{
return x_76;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_76, 0);
x_90 = lean_ctor_get(x_76, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_76);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_7 = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec_ref(x_8);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_7, 1);
x_19 = lean_ctor_get(x_7, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
x_25 = lean_int_dec_eq(x_20, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_7);
x_26 = l_Lean_instInhabitedExpr;
x_27 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___boxed), 12, 6);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_21);
lean_closure_set(x_28, 2, x_27);
lean_closure_set(x_28, 3, x_24);
lean_closure_set(x_28, 4, x_23);
lean_closure_set(x_28, 5, x_20);
x_29 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_30 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_22, x_29, x_28, x_2, x_3, x_4, x_5, x_18);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = lean_box(0);
lean_ctor_set(x_7, 0, x_31);
return x_7;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_dec(x_7);
x_33 = lean_ctor_get(x_15, 0);
lean_inc(x_33);
lean_dec(x_15);
x_34 = lean_ctor_get(x_16, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_dec(x_16);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__3;
x_38 = lean_int_dec_eq(x_33, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = l_Lean_instInhabitedExpr;
x_40 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_41 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___boxed), 12, 6);
lean_closure_set(x_41, 0, x_39);
lean_closure_set(x_41, 1, x_34);
lean_closure_set(x_41, 2, x_40);
lean_closure_set(x_41, 3, x_37);
lean_closure_set(x_41, 4, x_36);
lean_closure_set(x_41, 5, x_33);
x_42 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_43 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_35, x_42, x_41, x_2, x_3, x_4, x_5, x_32);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_32);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_46 = !lean_is_exclusive(x_7);
if (x_46 == 0)
{
return x_7;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_7);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Int_Linear_Expr_norm(x_1);
lean_inc_ref(x_9);
x_10 = l_Int_Linear_Poly_toExpr(x_9);
x_11 = l_Int_Linear_beqExpr____x40_Init_Data_Int_Linear_3091913453____hygCtx___hyg_120_(x_1, x_10);
lean_dec_ref(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_inc_ref(x_3);
x_12 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_15, 0, x_3);
lean_inc_ref(x_1);
lean_inc_ref(x_15);
x_16 = l_Int_Linear_Expr_denoteExpr___redArg(x_15, x_1, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
lean_inc_ref(x_9);
x_19 = l_Int_Linear_Poly_denoteExpr___redArg(x_15, x_9, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_23 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__0;
x_24 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__1;
x_25 = l_Lean_Name_mkStr4(x_2, x_22, x_23, x_24);
x_26 = lean_box(0);
x_27 = l_Lean_mkConst(x_25, x_26);
x_28 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_29 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_9);
x_30 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_31 = l_Lean_mkApp4(x_27, x_13, x_28, x_29, x_30);
lean_inc(x_21);
x_32 = l_Lean_mkIntEq(x_17, x_21);
x_33 = l_Lean_Meta_mkExpectedPropHint(x_31, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_19, 0, x_35);
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
x_38 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__1;
x_39 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__0;
x_40 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1___closed__1;
x_41 = l_Lean_Name_mkStr4(x_2, x_38, x_39, x_40);
x_42 = lean_box(0);
x_43 = l_Lean_mkConst(x_41, x_42);
x_44 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
x_45 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_9);
x_46 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1___closed__0;
x_47 = l_Lean_mkApp4(x_43, x_13, x_44, x_45, x_46);
lean_inc(x_36);
x_48 = l_Lean_mkIntEq(x_17, x_36);
x_49 = l_Lean_Meta_mkExpectedPropHint(x_47, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_36);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_37);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_53 = !lean_is_exclusive(x_19);
if (x_53 == 0)
{
return x_19;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_19, 0);
x_55 = lean_ctor_get(x_19, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_19);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_57 = !lean_is_exclusive(x_16);
if (x_57 == 0)
{
return x_16;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_16, 0);
x_59 = lean_ctor_get(x_16, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_16);
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
lean_dec_ref(x_9);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_61 = !lean_is_exclusive(x_12);
if (x_61 == 0)
{
return x_12;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_12, 0);
x_63 = lean_ctor_get(x_12, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_12);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_8);
return x_66;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_7 = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0;
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__1), 8, 2);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1;
x_15 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_11, x_14, x_13, x_2, x_3, x_4, x_5, x_9);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
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
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin, lean_io_mk_world());
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
